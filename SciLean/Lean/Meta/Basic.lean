import Lean
import Batteries.Lean.Expr

import SciLean.Lean.Expr
import SciLean.Lean.Array

namespace Lean

/-- Does free variable `x` uses free variable `y` in its type or value?
-/
def FVarId.usesFVar (x y : FVarId) : MetaM Bool := do
  if (← x.getType).containsFVar y then
    return true
  else
    match (← x.getValue?) with
    | .none => return false
    | .some val => return val.containsFVar y


namespace Meta

variable {m} [Monad m] [MonadEnv m] [MonadError m]


def getConstExplicitArgIds (constName : Name) : m (Array Nat) := do
  let info ← getConstInfo constName
  return info.type.explicitArgIds

def getConstArity (constName : Name) : m Nat := do
  let info ← getConstInfo constName
  return info.type.getNumHeadForalls

def getConstArgNames (constName : Name) (fixAnonymousNames := false) : m (Array Name) := do
  let info ← getConstInfo constName
  return getArgNames info.type #[] 0
where
  getArgNames (e : Expr) (names : Array Name) (i : Nat) : Array Name :=
    match e with
    | .forallE name _ body _ =>
      if ¬fixAnonymousNames then
        getArgNames body (names.push name) i
      else
        if name.hasMacroScopes then
          getArgNames body (names.push (name.eraseMacroScopes.appendAfter (toString i))) (i+1)
        else
          getArgNames body (names.push name) i
    | _ => names

open Lean Meta in
def getConstArgId (thmName argName : Name) : MetaM Nat := do
  let info ← getConstInfo thmName
  forallTelescope info.type fun xs _ => do
    if let .some id ← xs.findIdxM? (fun x => do return (← x.fvarId!.getUserName) == argName) then
      return id
    else
      throwError "argId: {argName} is not an argument of {thmName}"


/-- Returns name of the head function of an expression

TODO: See through FunLike.coe

Example:
  `getFunHeadConst? q(fun x => x + x) = HAdd.hAdd`
  `getFunHeadConst? q(fun x y => x + y) = HAdd.hAdd`
  `getFunHeadConst? q(HAdd.hAdd 1) = HAdd.hAdd`
  `getFunHeadConst? q(fun xy : X×Y => xy.2) = Prod.snd`
  `getFunHeadConst? q(fun f x => f x) = none`
-/
def getFunHeadConst? (e : Expr) : MetaM (Option Name) :=
  match e.consumeMData with
  | .const name _ => return name
  | .app f _ => return f.getAppFn'.constName?
  | .lam _ _ b _ => return b.letBodyRec'.getAppFn'.constName?
  | .proj structName idx _ => do
     let .some info := getStructureInfo? (← getEnv) structName
       | return none
     return info.getProjFn? idx
  | _ => return none


/-- Changes structure projection back to function application. Left unchanged if not a projection.

For example `proj ``Prod 0 xy` is changed to `mkApp ``Prod.fst #[xy]`.
-/
def revertStructureProj (e : Expr) : MetaM Expr :=
  match e with
  | .proj name i struct => do
    let some info := getStructureInfo? (← getEnv) name
      | panic! "structure expected"
    let some projFn := info.getProjFn? i
      | panic! "valid projection index expected"
    mkAppM projFn #[struct]
  | _ => return e

/-- Is `e` in the form `foo x₀ .. xₙ` where `foo` is some constant

  It returns only explicit arguments and the original expression should be recoverable by `mkAppM foo #[x₀, .., xₙ]`
  -/
def getExplicitArgs (e : Expr) : MetaM (Option (Name×Array Expr)) := do
  let .some (funName, _) := e.getAppFn.const?
    | return none

  let n ← getConstArity funName
  let explicitArgIds ← getConstExplicitArgIds funName

  let args := e.getAppArgs

  let explicitArgs := explicitArgIds.foldl (init := #[])
    λ a id => if h : id < args.size then a.push args[id] else a

  return (funName, explicitArgs)


/-- Eta expansion, but adds at most `n` binders
-/
def etaExpandN (e : Expr) (n : Nat) : MetaM Expr :=
  withDefault do forallTelescopeReducing (← inferType e) fun xs _ => mkLambdaFVars xs[0:n] (mkAppN e xs[0:n])

/-- Eta expansion, it also beta reduces the body
-/
def etaExpand' (e : Expr) : MetaM Expr :=
  withDefault do forallTelescopeReducing (← inferType e) fun xs _ => mkLambdaFVars xs (mkAppN e xs).headBeta

/-- Ensures that function is eta expanded -/
def ensureEtaExpanded (e : Expr) : MetaM Expr := do
  if e.isLambda then
    return e
  else
    let .forallE n t _ _ ← inferType e | throwError "function expected"
    return .lam n t (e.app (.bvar 0)) default


/--
  Same as `mkAppM` but does not leave trailing implicit arguments.

  For example for `foo : (X : Type) → [OfNat 0 X] → X` the ``mkAppNoTrailingM `foo #[X]`` produces `foo X : X` instead of `@foo X : [OfNat 0 X] → X`
-/
def mkAppNoTrailingM (constName : Name) (xs : Array Expr) : MetaM Expr := do

  let n ← getConstArity constName
  let explicitArgIds ← getConstExplicitArgIds constName

  -- number of arguments to apply
  let argCount := explicitArgIds[xs.size]? |>.getD n

  let mut args : Array (Option Expr) := Array.replicate argCount none
  for i in [0:xs.size] do
    args := args.set! explicitArgIds[i]! (.some xs[i]!)

  mkAppOptM constName args

def mkAppFoldrM (const : Name) (xs : Array Expr) : MetaM Expr := do
  if xs.size = 0 then
    return default
  if xs.size = 1 then
    return xs[0]!
  else
    xs.joinrM pure
      λ x p =>
        mkAppM const #[x,p]

def mkAppFoldlM (const : Name) (xs : Array Expr) : MetaM Expr := do
  if xs.size = 0 then
    return default
  if xs.size = 1 then
    return xs[0]!
  else
    xs.joinlM pure
      λ p x =>
        mkAppM const #[p,x]

/--
For `#[x₁, .., xₙ]` create `(x₁, .., xₙ)`.
-/
def mkProdElem (xs : Array Expr) (mk := ``Prod.mk) : MetaM Expr := mkAppFoldrM mk xs

def mkProdFst (x : Expr) : MetaM Expr := mkAppM ``Prod.fst #[x]
def mkProdSnd (x : Expr) : MetaM Expr := mkAppM ``Prod.snd #[x]

/--
For `(x₀, .., xₙ₋₁)` return `xᵢ` but as a product projection.

We need to know the total size of the product to be considered.

For example for `xyz : X × Y × Z`
  - `mkProdProj xyz 1 3` returns `xyz.snd.fst`.
  - `mkProdProj xyz 1 2` returns `xyz.snd`.
-/
def mkProdProj (x : Expr) (i : Nat) (n : Nat) (fst := ``Prod.fst) (snd := ``Prod.snd) : MetaM Expr := do
  -- let X ← inferType x
  -- if X.isAppOfArity ``Prod 2 then
  match i, n with
  | _, 0 => pure x
  | _, 1 => pure x
  | 0, _ => mkAppM fst #[x]
  | i'+1, n'+1 => mkProdProj (← withTransparency .all <| mkAppM snd #[x]) i' n'
  -- else
  --   if i = 0 then
  --     return x
  --   else
  --     throwError "Failed `mkProdProj`, can't take {i}-th element of {← ppExpr x}. It has type {← ppExpr X} which is not a product type!"


def mkProdSplitElem (xs : Expr) (n : Nat) (fst := ``Prod.fst) (snd := ``Prod.snd) : MetaM (Array Expr) :=
  (Array.replicate n 0)
    |>.mapIdx (λ i _ => i)
    |>.mapM (λ i => mkProdProj xs i n fst snd)

def mkUncurryFun (n : Nat) (f : Expr) (mk := ``Prod.mk) (fst := ``Prod.fst) (snd := ``Prod.snd) : MetaM Expr := do
  if n ≤ 1 then
    return f
  forallTelescope (← inferType f) λ xs _ => do
    let xs := xs[0:n]

    let xProdName := Name.mkSimple <| ← xs.foldlM (init:="") λ n x =>
      do return (n ++ toString (← x.fvarId!.getUserName).eraseMacroScopes)
    let xProdType ← inferType (← mkProdElem xs mk)

    withLocalDecl xProdName default xProdType λ xProd => do
      let xs' ← mkProdSplitElem xProd n fst snd
      mkLambdaFVars #[xProd] (← mkAppM' f xs').headBeta


/-- Takes lambda function `fun x => b` and splits it into composition of two functions.

  Example:
    fun x => f (g x)      ==>   f ∘ g
    fun x => f x + c      ==>   (fun y => y + c) ∘ f
    fun x => f x + g x    ==>   (fun (y₁,y₂) => y₁ + y₂) ∘ (fun x => (f x, g x))
    fun x i => f (g₁ x i) (g₂ x i) i  ==>   (fun (y₁,y₂) i => f y₁ y₂ i) ∘' (fun x i => (g₁ x i, g₂ x i))
    fun x i => x i        ==>   (fun x i => x i) ∘' (fun x i => x)
 -/
def splitLambdaToComp (e : Expr) (mk := ``Prod.mk) (fst := ``Prod.fst) (snd := ``Prod.snd) : MetaM (Expr × Expr) := do
  match e with
  | .lam name _ _ _ =>
    let e ← instantiateMVars e
    lambdaTelescope e λ xs b => do
      let x := xs[0]!
      let b := b.instantiate1 x
      let xId := x.fvarId!

      let ys := b.getAppArgs
      let mut f := b.getAppFn

      let mut lctx ← getLCtx
      let instances ← getLocalInstances

      let mut ys' : Array Expr := #[]
      let mut zs  : Array Expr := #[]

      if f.containsFVar xId then
        let zId ← withLCtx lctx instances mkFreshFVarId
        lctx := lctx.mkLocalDecl zId (name) (← inferType f)
        let z := Expr.fvar zId
        zs  := zs.push z
        ys' := ys'.push f
        f := z

      for y in ys, i in [0:ys.size] do
        if y.containsFVar xId then
          let zId ← withLCtx lctx instances mkFreshFVarId
          lctx := lctx.mkLocalDecl zId (name.appendAfter (toString i)) (← inferType y)
          let z := Expr.fvar zId
          zs  := zs.push z
          ys' := ys'.push y
          f := f.app z
        else
          f := f.app y

      let y' ← mkProdElem ys' mk
      let g  ← mkLambdaFVars xs y'

      f ← withLCtx lctx instances (mkLambdaFVars (zs ++ xs[1:]) f)
      f ← mkUncurryFun zs.size f mk fst snd

      return (f, g)

  | _ => throwError "Error in `splitLambdaToComp`, not a lambda function!"


inductive LambdaSplit where
  /-- Result of splitting a lambda function as `fun x => f (g x)` -/
  | comp (f g : Expr)
  /-- Result of splitting a lambda function as `fun x i₁ ... iₙ => f (g x i₁ ... iₙ)` -/
  | piComp (f g : Expr) (comp : Expr → Expr → Expr)

/--
This function decomposes function as
```
fun x i₁ .. iₙ => b
=
fun x i₁ ... iₙ => f (g x) i₁ ... iₙ
=
f ∘ g
```

For example, for `f' : Y → I → Z` and `g' : X → I → Y`
```
fun x i => f' (g' x i) i
=
fun x i => f'' (g' x) i
=
f'' ∘ g'
```
where `f'' = fun (y' : I → Y) i => f' (y' i) i`
-/
def splitHighOrderLambdaToComp (e : Expr) (mk := ``Prod.mk) (fst := ``Prod.fst) (snd := ``Prod.snd) : MetaM (Expr × Expr) := do
  match e with
  | .lam name _ _ _ =>
    let e ← instantiateMVars e
    lambdaTelescope e λ xs b => do
      let x := xs[0]!
      let b := b.instantiate1 x
      let xId := x.fvarId!

      let ys := b.getAppArgs
      let mut f := b.getAppFn

      let mut lctx ← getLCtx
      let instances ← getLocalInstances

      -- trailing arguments
      let is := xs[1:].toArray

      -- `ys` that depend on `x`
      let mut ys' : Array Expr := #[]
      -- `ys` that depend on `x` and all `is` that appear are turned into lambda
      let mut ys'' : Array Expr := #[]
      -- fvars for `y` that are abstracted over `is`
      let mut yFVars : Array Expr := #[]
      -- `yVars` with corresponding `is` applied
      let mut yVals  : Array Expr := #[]

      if f.containsFVar xId then
        let is' := is.filter (fun i => f.containsFVar i.fvarId!)
        let yFVarType ← mkLambdaFVars is' (← inferType f)
        let yId ← withLCtx lctx instances mkFreshFVarId
        lctx := lctx.mkLocalDecl yId (name) yFVarType
        let yFVar := Expr.fvar yId
        let yVal := mkAppN yFVar is'
        yFVars := yFVars.push yFVar
        yVals := yVals.push yVal
        ys' := ys'.push f
        ys'' := ys''.push (← mkLambdaFVars is' f)
        f := yVal

      for y in ys, i in [0:ys.size] do
        if y.containsFVar xId then
          -- is it repeated argument?
          if let .some i ← ys'.findIdxM? (fun y' => isDefEq y y') then
            -- reuse already introduce fvar
            f := f.app yVals[i]!
          else

            -- filter trailing arguments that appear in this `y`
            let is' := is.filter (fun i => y.containsFVar i.fvarId!)
            let yFVarType ← mkForallFVars is' (← inferType y)

            -- introduce new fvar
            let yId ← withLCtx lctx instances mkFreshFVarId
            lctx := lctx.mkLocalDecl yId (name.appendAfter (toString i)) yFVarType
            let yFVar := Expr.fvar yId
            let yVal := mkAppN yFVar is'
            yFVars := yFVars.push yFVar
            yVals := yVals.push yVal
            ys' := ys'.push y
            ys'' := ys''.push (← mkLambdaFVars is' y)
            f := f.app yVal
        else
          f := f.app y

      let y' ← mkProdElem ys'' mk
      let g  ← mkLambdaFVars #[x] y'

      f ← withLCtx lctx instances (mkLambdaFVars (yFVars ++ is) f)
      f ← mkUncurryFun yFVars.size f mk fst snd

      return (f, g)

  | _ => throwError "Error in `splitLambdaToComp`, not a lambda function!"



/--
This function finds decomposition:
```
fun x i₁ .. iₙ => b
=
fun x i₁ ... iₙ => f (g x i₁ ... iₙ) i₁ ... iₙ
```
-/
def elemWiseSplitHighOrderLambdaToComp (e : Expr) (mk := ``Prod.mk) (fst := ``Prod.fst) (snd := ``Prod.snd) : MetaM (Expr × Expr) := do
  match e with
  | .lam name _ _ _ =>
    let e ← instantiateMVars e
    lambdaTelescope e λ xs b => do
      let x := xs[0]!
      let b := b.instantiate1 x
      let xId := x.fvarId!

      let ys := b.getAppArgs
      let mut f := b.getAppFn

      let mut lctx ← getLCtx
      let instances ← getLocalInstances

      -- trailing arguments
      let is := xs[1:].toArray

      -- `ys` that depend on `x`
      let mut ys' : Array Expr := #[]
      -- fvars for `y` that are abstracted over `is`
      let mut yFVars : Array Expr := #[]

      if f.containsFVar xId then
        let yFVarType ← inferType f
        let yId ← withLCtx lctx instances mkFreshFVarId
        lctx := lctx.mkLocalDecl yId (name) yFVarType
        let yFVar := Expr.fvar yId
        yFVars := yFVars.push yFVar
        ys' := ys'.push f
        f := yFVar

      for y in ys, i in [0:ys.size] do
        if y.containsFVar xId then
          -- is it repeated argument?
          if let .some i ← ys'.findIdxM? (fun y' => isDefEq y y') then
            -- reuse already introduce fvar
            f := f.app yFVars[i]!
          else

            let yFVarType ← inferType y

            -- introduce new fvar
            let yId ← withLCtx lctx instances mkFreshFVarId
            lctx := lctx.mkLocalDecl yId (name.appendAfter (toString i)) yFVarType
            let yFVar := Expr.fvar yId
            yFVars := yFVars.push yFVar
            ys' := ys'.push y
            f := f.app yFVar
        else
          f := f.app y

      let y' ← mkProdElem ys' mk
      let g  ← mkLambdaFVars xs y'

      f ← withLCtx lctx instances (mkLambdaFVars (yFVars ++ is) f)
      f ← mkUncurryFun yFVars.size f mk fst snd

      return (f, g)

  | _ => throwError "Error in `splitLambdaToComp`, not a lambda function!"

/-- Make local declarations is we have an array of names and types. -/
def mkLocalDecls [MonadControlT MetaM n] [Monad n]
  (names : Array Name) (bi : BinderInfo) (types : Array Expr) : Array (Name × BinderInfo × (Array Expr → n Expr)) :=
  types.mapIdx (fun i type => (names[i]!, bi, fun _ : Array Expr => pure type))

/-- Simpler version of `withLocalDecls` that can't deal with dependent types but has simpler signature -/
def withLocalDecls' [Inhabited α] [MonadControlT MetaM n] [Monad n]
  (names : Array Name) (bi : BinderInfo) (types : Array Expr) (k : Array Expr → n α) : n α :=
  withLocalDecls (mkLocalDecls names bi types) k


private partial def withLetDeclsImpl
  (names : Array Name) (vals : Array Expr) (k : Array Expr → MetaM α) : MetaM α :=
  loop #[]
where
  loop (acc : Array Expr) : MetaM α := do
    let i := acc.size
    if h : i < vals.size then
      let val := vals[i]
      let type ← inferType val
      withLetDecl names[i]! type val fun x => loop (acc.push x)
    else
      k acc

def withLetDecls [MonadControlT MetaM n] [Monad n]
  (names : Array Name) (vals : Array Expr) (k : Array Expr → n α) : n α :=
  map1MetaM (fun k => withLetDeclsImpl names vals k) k


-- @[inline] def map3MetaM [MonadControlT MetaM m] [Monad m]
--   (f : forall {α}, (β → γ → δ → MetaM α) → MetaM α)
--   {α} (k : β → γ → δ → m α) : m α :=
--   controlAt MetaM fun runInBase => f (fun b c d => runInBase <| k b c d)

@[inline] def map4MetaM [MonadControlT MetaM m] [Monad m]
  (f : forall {α}, (β → γ → δ → ε → MetaM α) → MetaM α)
  {α} (k : β → γ → δ → ε → m α) : m α :=
  controlAt MetaM fun runInBase => f (fun b c d e => runInBase <| k b c d e)


private def letTelescopeImpl (e : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α :=
  lambdaLetTelescope e λ xs b => do
    if let .some i ← xs.findIdxM? (λ x => do pure !(← x.fvarId!.isLetVar)) then
      k xs[0:i] (← mkLambdaFVars xs[i:] b)
    else
      k xs b

variable [MonadControlT MetaM n] [Monad n]

def letTelescope (e : Expr) (k : Array Expr → Expr → n α) : n α :=
  map2MetaM (fun k => letTelescopeImpl e k) k


private partial def flatLetTelescopeImpl {α} (fuel : Nat) (e : Expr) (k : Array Expr → Expr → MetaM α) (splitPairs := true) : MetaM α := do
  if fuel = 0 then
    k #[] e
  else
  match e with
  | .app f x =>

    -- we want to normalize let bindings only on value level
    -- also it was blowing the stack on complicated type class projections
    if ¬((← inferType x).isType) then
      flatLetTelescopeImpl (fuel-1) f λ xs f' =>
        flatLetTelescopeImpl (fuel-1) x λ ys x' =>
          k (xs.append ys) (.app f' x')
    else
      k #[] e

  | .letE n t v b _ =>
    flatLetTelescopeImpl (fuel-1) v λ xs v' => do

      -- TODO: Generalized to any structure constructor
      match splitPairs, v'.app4? ``Prod.mk with
      | true, .some (Fst, Snd, fst, snd) =>
        withLetDecl (n.appendAfter "₁") Fst fst λ fst' =>
          withLetDecl (n.appendAfter "₂") Snd snd λ snd' => do
            let p ← mkAppM ``Prod.mk #[fst', snd']
            flatLetTelescopeImpl (fuel-1) (← mkLetFVars #[fst', snd'] (b.instantiate1 p)) λ ys b' =>
              k (xs.append ys) b'

      | _, _ =>
        withLetDecl n t v' λ v'' =>
          flatLetTelescopeImpl (fuel-1) (b.instantiate1 v'') λ ys b' =>
            k ((xs.push v'').append ys) b'

  | .lam n t b bi =>
    withLocalDecl n bi t λ x =>
      flatLetTelescopeImpl (fuel-1) (b.instantiate1 x) λ ys b' => do

        -- find where can we split ys
        let mut i := 0
        for y in ys do
          if let .some yVal ← y.fvarId!.getValue? then
            if yVal.containsFVar x.fvarId! then
              break
          i := i + 1


        k ys[0:i] (← mkLambdaFVars #[x] (← mkLetFVars ys[i:] b'))

  | .mdata _ e =>
    flatLetTelescopeImpl (fuel-1) e k

  | _ =>
    k #[] e


/-- Telescope for let bindings but it flattens let bindings first

Example:
```
let a :=
  let b := (10, 12)
  20
f a b
```

It will run `k #[b₁, b₂, a] (f a (b₁,b₂))` where `b₁ := 10, b₂ := 12, a := 20`.


If `splitPairs` is `false`, it will run `k #[b, a] (f a b)`
-/
def flatLetTelescope (fuel : Nat) (e : Expr) (k : Array Expr → Expr → n α) (splitPairs := true) : n α :=
  map2MetaM (fun k => flatLetTelescopeImpl fuel e k splitPairs) k

/-- Flattens let bindings and splits let binding of pairs.

Example:
```
let a :=
  let b := (10, 12)
  (b.1, 3 * b.2)
a.2
```
is rewritten to
```
let b₁ := 10;
let b₂ := 12;
let a₁ := (b₁, b₂).fst;
let a₂ := 3 * (b₁, b₂).snd;
(a₁, a₂).snd
```
-/
def flattenLet (fuel : Nat) (e : Expr) (splitPairs := true) : MetaM Expr :=
  flatLetTelescope (splitPairs:=splitPairs) fuel e λ xs e' =>
    mkLetFVars xs e'


/-- Reduces structure projection but it preserves let bindings unlike `Lean.Meta.reduceProj?`.
-/
def reduceProj?' (e : Expr) : MetaM (Option Expr) := do
  match e with
  | Expr.proj _ _ (.fvar _) => return none -- do not reduce projections on fvars
  | Expr.proj _ i c =>
    letTelescope c λ xs b => do
      let some b ← Meta.project? b i
        | return none
      mkLambdaFVars xs b
  | _               => return none


/-- Reduces structure projection function but it preserves let bindings unlike `Lean.Meta.Simp.reduceProjFn?`.

  TODO: Maybe move to SimpM and recover unfolding of user specified classes
-/
def reduceProjFn?' (e : Expr) : MetaM (Option Expr) := do
  matchConst e.getAppFn (fun _ => pure none) fun cinfo _ => do
    match (← getProjectionFnInfo? cinfo.name) with
    | none => return none
    | some projInfo =>
      /- Helper function for applying `reduceProj?` to the result of `unfoldDefinition?` -/
      let reduceProjCont? (e? : Option Expr) : MetaM (Option Expr) := do
        match e? with
        | none   => pure none
        | some e =>
          match (← reduceProj?' e.getAppFn) with
          | some f => return some (mkAppN f e.getAppArgs)
          | none   => return none
      if projInfo.fromClass then
        -- There was a special case in the simplifiedr step
        -- -`class` projection
        -- if (← read).isDeclToUnfold cinfo.name then
        unless e.getAppNumArgs > projInfo.numParams do
          return none
        let major := e.getArg! projInfo.numParams
        unless ← isConstructorApp major do
          return none
        reduceProjCont? (← withDefault <| unfoldDefinition? e)
      else
        -- `structure` projections
        reduceProjCont? (← unfoldDefinition? e)


namespace ReduceProjOfCtor

private inductive Projection where
| proj (typeName : Name) (idx : Nat)
| function (f : Expr) (idx : Nat)

private def Projection.index (p : Projection) : Nat :=
  match p with
  | .proj _ idx => idx
  | .function _ idx => idx

private def peelOfProjections (e : Expr) (projections : List Projection := []) : MetaM (Expr × List Projection) :=
  match e with
  | Expr.proj typeName idx e' => peelOfProjections e' ((.proj typeName idx) :: projections)
  | .app f x =>
    matchConst f.getAppFn (fun _ => pure (e,projections)) fun cinfo _ => do
      match (← getProjectionFnInfo? cinfo.name) with
      | none => return (e,projections)
      | some projInfo =>
        if projInfo.numParams = f.getAppNumArgs then
          peelOfProjections x ((.function f projInfo.i) :: projections )
        else
          pure (e,projections)
  | .mdata _ e' => peelOfProjections e' projections
  | e' => pure (e',projections)


private def applyProjections (e : Expr) : List Projection → Expr
  | [] => e
  | (.proj typeName idx) :: ps => applyProjections (.proj typeName idx e) ps
  | (.function f _) :: ps => applyProjections (f.app e) ps

private def reduceProjections (e : Expr) (projections : List Projection) : CoreM Expr :=
  match projections with
  | [] => pure e
  | p :: ps =>
    matchConstCtor e.getAppFn (fun _ => pure (applyProjections e projections)) fun info _ => do
      if e.getAppNumArgs = info.numParams + info.numFields then
        reduceProjections (e.getArg! (info.numParams + p.index)) ps
      else
        pure (applyProjections e projections)


/-- Return none if no projections happen
-/
private def reduceProjections? (e : Expr) (projections : List Projection) : CoreM (Option Expr) :=
  match projections with
  | [] => pure none
  | p :: ps =>
    matchConstCtor e.getAppFn (fun _ => pure none) fun info _ => do
      if e.getAppNumArgs = info.numParams + info.numFields then
        reduceProjections (e.getArg! (info.numParams + p.index)) ps
      else
        pure none


end ReduceProjOfCtor

open ReduceProjOfCtor in
/-- Reduces structure projection of explicit constructors

Examples:
```
((a,b),c).1.2  ==> b
```

```
((a,b),c).1.2.1  ==> b.1
```
even if `b` is a free variable introduced by a let binding
-/
def reduceProjOfCtor (e : Expr) : MetaM Expr := do
  let (e',ps) ← peelOfProjections e
  reduceProjections e' ps

open ReduceProjOfCtor in
/-- Reduces structure projection of explicit constructors

For example, `(x,y,z).2.1.1` reduces to `y.1` even if `y` is reducible definition
or let fvar.
-/
def reduceProjOfCtor? (e : Expr) : MetaM (Option Expr) := do
  let (e',ps) ← peelOfProjections e
  reduceProjections? e' ps

open Qq

def isTypeQ (e : Expr) : MetaM (Option ((u : Level) × Q(Type $u))) := do
  let u ← mkFreshLevelMVar
  let .some e ← checkTypeQ e q(Type $u)
    | return none
  return .some ⟨u, e⟩

def _root_.Lean.LocalContext.toString (lctx : LocalContext) : MetaM String :=
  lctx.decls.toArray.joinlM
    (fun decl? => do
      let .some decl := decl? | return ""
      return s!"{decl.userName} : {← ppExpr decl.type}")
    (fun a b => pure (a++"\n"++b))



def mkCurryFun (n : Nat) (f : Expr) (mk := ``Prod.mk) (fst := ``Prod.fst) (snd := ``Prod.snd) : MetaM Expr := do
  if n ≤ 1 then
    return f
  else
    let .forallE xName xType _ _ := (← inferType f)
      | throwError "can't curry `{← ppExpr f}` not a function"

    withLocalDecl xName .default xType fun x => do
      let xs ← mkProdSplitElem x n fst snd
      let xNames := xs.mapIdx fun i _ => xName.appendAfter (toString i)
      let xTypes ← xs.mapM inferType
      withLocalDecls' xNames .default xTypes fun xVars => do
        let x' ← mkProdElem xVars mk
        let b := (f.app x').headBeta

        let b ← Meta.transform b
          (post := fun e => do
            if (← isType e)
            then return .done e
            else return .done (← reduceProjOfCtor e))

        mkLambdaFVars xVars b
