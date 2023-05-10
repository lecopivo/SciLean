import Lean
import Std.Lean.Expr

import SciLean.Lean.Expr 
import SciLean.Lean.Array

namespace Lean.Meta

variable {m} [Monad m] [MonadEnv m] [MonadError m]


def getConstExplicitArgIds (constName : Name) : m (Array Nat) := do
  let info ← getConstInfo constName
  return info.type.explicitArgIds

def getConstArity (constName : Name) : m Nat := do
  let info ← getConstInfo constName
  return info.type.forallArity

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



/--
  Same as `mkAppM` but does not leave trailing implicit arguments.

  For example for `foo : (X : Type) → [OfNat 0 X] → X` the ``mkAppNoTrailingM `foo #[X]`` produces `foo X : X` instead of `@foo X : [OfNat 0 X] → X`
-/
def mkAppNoTrailingM (constName : Name) (xs : Array Expr) : MetaM Expr := do

  let n ← getConstArity constName
  let explicitArgIds ← getConstExplicitArgIds constName

  -- number of arguments to apply
  let argCount := explicitArgIds[xs.size]? |>.getD n

  let mut args : Array (Option Expr) := Array.mkArray argCount none
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
def mkProdElem (xs : Array Expr) : MetaM Expr := mkAppFoldrM ``Prod.mk xs

def mkProdFst (x : Expr) : MetaM Expr := mkAppM ``Prod.fst #[x]
def mkProdSnd (x : Expr) : MetaM Expr := mkAppM ``Prod.snd #[x]

/--
For `(x₀, .., xₙ₋₁)` return `xᵢ` but as a product projection.

We need to know the total size of the product to be considered.

For example for `xyz : X × Y × Z`
  - `mkProdProj xyz 1 3` returns `xyz.snd.fst`.
  - `mkProdProj xyz 1 2` returns `xyz.snd`.
-/
def mkProdProj (x : Expr) (i : Nat) (n : Nat) : MetaM Expr := do
  let X ← inferType x
  if X.isAppOfArity ``Prod 2 then
     match i, n with
     | _, 0 => pure x
     | _, 1 => pure x
     | 0, _ => mkAppM ``Prod.fst #[x]
     | i'+1, n'+1 => mkProdProj (← mkAppM ``Prod.snd #[x]) i' n'
  else
    if i = 0 then
      return x
    else
      throwError "Failed `mkProdProj`, can't take {i}-th element of {← ppExpr x}. It has type {← ppExpr X} which is not a product type!"


def mkProdSplitElem (xs : Expr) (n : Nat) : MetaM (Array Expr) := 
  (Array.mkArray n 0)
    |>.mapIdx (λ i _ => i.1)
    |>.mapM (λ i => mkProdProj xs i n)

def mkUncurryFun (n : Nat) (f : Expr) : MetaM Expr := do
  if n ≤ 1 then
    return f
  forallTelescope (← inferType f) λ xs _ => do
    let xs := xs[0:n]

    let xProdName : String ← xs.foldlM (init:="") λ n x => 
      do return (n ++ toString (← x.fvarId!.getUserName))
    let xProdType ← inferType (← mkProdElem xs)

    withLocalDecl xProdName default xProdType λ xProd => do
      let xs' ← mkProdSplitElem xProd n
      mkLambdaFVars #[xProd] (← mkAppM' f xs').headBeta


@[inline] def map3MetaM [MonadControlT MetaM m] [Monad m]
  (f : forall {α}, (β → γ → δ → MetaM α) → MetaM α) 
  {α} (k : β → γ → δ → m α) : m α :=
  controlAt MetaM fun runInBase => f (fun b c d => runInBase <| k b c d)

@[inline] def map4MetaM [MonadControlT MetaM m] [Monad m] 
  (f : forall {α}, (β → γ → δ → ε → MetaM α) → MetaM α) 
  {α} (k : β → γ → δ → ε → m α) : m α :=
  controlAt MetaM fun runInBase => f (fun b c d e => runInBase <| k b c d e)


private def letTelescopeImpl (e : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α := 
  lambdaLetTelescope e λ xs b => do
    if let .some i ← xs.findIdxM? (λ x => do pure ¬(← x.fvarId!.isLetVar)) then
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
        unless major.isConstructorApp (← getEnv) do
          return none
        reduceProjCont? (← withDefault <| unfoldDefinition? e)
      else
        -- `structure` projections
        reduceProjCont? (← unfoldDefinition? e)

