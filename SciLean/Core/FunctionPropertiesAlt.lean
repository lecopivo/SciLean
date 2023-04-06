import SciLean.Core.Defs
import SciLean.Core.Meta.FunctionProperty
-- import SciLean.Core.Meta.RewriteBy

import SciLean.Tactic.AutoDiff

import SciLean.Data.ArraySet

import SciLean.Core.FunctionTheorems


namespace SciLean

set_option linter.unusedVariables false 

open Lean Parser.Term Lean.Elab Meta

#check mkApp

def uncurryN' {F : Type} {Xs Y : outParam Type} 
  (n : Nat) (f : F) [Prod.Uncurry n F Xs Y] 
  := uncurryN n f


def _root_.Lean.Meta.getConstExplicitArgIdx (constName : Name) : MetaM (Array Nat) := do
  let info ← getConstInfo constName

  let (_, explicitArgIdx) ← forallTelescope info.type λ Xs _ => do
    Xs.foldlM (init := (0,(#[] : Array Nat))) 
      λ (i, ids) X => do 
        if (← X.fvarId!.getBinderInfo).isExplicit then
          pure (i+1, ids.push i)
        else
          pure (i+1, ids)

  return explicitArgIdx

def _root_.Lean.Meta.getConstArity (constName : Name) : MetaM Nat := do
  let info ← getConstInfo constName
  return info.type.forallArity

/--
  Same as `mkAppM` but does not leave trailing implicit arguments.

  For example for `foo : (X : Type) → [OfNat 0 X] → X` the ``mkAppNoTrailingM `foo #[X]`` produces `foo X : X` instead of `@foo X : [OfNat 0 X] → X`
-/
def _root_.Lean.Meta.mkAppNoTrailingM (constName : Name) (xs : Array Expr) : MetaM Expr := do

  let n ← getConstArity constName
  let explicitArgIds ← getConstExplicitArgIdx constName

  -- number of arguments to apply
  let argCount := explicitArgIds[xs.size]? |>.getD n

  let mut args : Array (Option Expr) := Array.mkArray argCount none
  for i in [0:xs.size] do
    args := args.set! explicitArgIds[i]! (.some xs[i]!)

  mkAppOptM constName args


@[inline]
def _root_.Array.partitionIdxM {m} [Monad m] (p : α → m Bool) (as : Array α) : m (Array α × Array α × Array (Sum Nat Nat)) := do
  let mut bs := #[]
  let mut cs := #[]
  let mut ids : Array (Sum Nat Nat) := #[]
  let mut i := 0
  let mut j := 0
  for a in as do
    if ← p a then
      bs := bs.push a
      ids := ids.push (.inl i)
      i := i + 1
    else
      cs := cs.push a
      ids := ids.push (.inr j)
      j := j + 1
  return (bs, cs, ids)

def _root_.Array.merge (ids : Array (Sum Nat Nat)) (bs cs : Array α) [Inhabited α] : Array α :=
  ids.map λ id => 
    match id with
    | .inl i => bs[i]!
    | .inr j => cs[j]!

variable [MonadControlT MetaM n] [Monad n]

#check map2MetaM

@[inline] def _root_.Lean.Meta.map3MetaM [MonadControlT MetaM m] [Monad m] (f : forall {α}, (β → γ → δ → MetaM α) → MetaM α) {α} (k : β → γ → δ → m α) : m α :=
  controlAt MetaM fun runInBase => f (fun b c d => runInBase <| k b c d)

@[inline] def _root_.Lean.Meta.map4MetaM [MonadControlT MetaM m] [Monad m] (f : forall {α}, (β → γ → δ → ε → MetaM α) → MetaM α) {α} (k : β → γ → δ → ε → m α) : m α :=
  controlAt MetaM fun runInBase => f (fun b c d e => runInBase <| k b c d e)

private def createCompositionImpl (e : Expr) (xs : Array Expr) (k : (T : Expr) → (t : Expr) → (ys : Array Expr) → (e' : Expr) → MetaM α) : MetaM α := do
  withLocalDecl `T .implicit (mkSort levelOne) λ T => do
    withLocalDecl `t .default T λ t => do
      
      let xIds := xs.map λ x => x.fvarId!

      -- We are not using `withLocalDecls` as it requires `Inhabited α` and that 
      -- does not play well with map4MetaM
      let mut lctx ← getLCtx
      let mut i := lctx.numIndices
      let mut ys : Array Expr := .mkEmpty xs.size
      for id in xIds do 
        let name ← id.getUserName
        let bi ← id.getBinderInfo 
        let type ← mkArrow T (← id.getType)
        let yId ← mkFreshFVarId
        ys := ys.push (mkFVar yId)
        lctx := lctx.addDecl (mkLocalDeclEx i yId name type bi)
        i := i + 1

      withLCtx lctx (← getLocalInstances) do
        let yts ← ys.mapM λ y => mkAppM' y #[t]
        let replacePairs := xIds.zip yts
        let e' := replacePairs.foldl (init:=e) λ e (id,yt) => e.replaceFVarId id yt

        k T t ys e'

/-- 
  For every free variable `x : X` introduce `y : T → X` and replace every `x` in `e` with `y t`.

  Then call `k` on `e` providing the newly introduces `T`, `t`, `ys`
  -/
def createComposition  (e : Expr) (xs : Array Expr) (k : (T : Expr) → (t : Expr) → (ys : Array Expr) → (e' : Expr) → n α) : n α := 
  map4MetaM (fun k => createCompositionImpl e xs k) k


-- def createCompositionOtherImpl (e : Expr) (xs : Array Expr) (other : Array Expr) 
--   (k : (T : Expr) → (t : Expr) →  (ys : Array Expr) → (other' : Array Expr) → (e' : Expr) → MetaM α) : MetaM α := do

/-- 
  For every free variable `x : X`, elements of `xs`, introduce `y : T → X`, elements of `ys`, and: 
    - replace every `x` in `e` with `y t` 
    - replace every `x` in `other` with `y`.
  where `{T : Type} (t : T)` are newly introduced free variables

  Then call `k` on `e` providing `T`, `t`, `ys` `other`

  NOTE: Most likely this operation makes sense only if `other` is a list of free variables
  -/
def createCompositionOther (e : Expr) (xs : Array Expr) (other : Array Expr) 
  (k : (T : Expr) → (t : Expr) →  (ys : Array Expr) → (other' : Array Expr) → (e' : Expr) → n α) : n α := do

  createComposition e xs λ T t ys e => do 
    
    let other := other.map λ e' => 
      e'.replace (λ e'' => Id.run do
        for (x, y) in xs.zip ys do
          if e'' == x then 
            return some y
        return none)

    k T t ys other e

/-- 
Applies `funName` to `e` but as a composition through arguments specified by `argIds`

This means, for `e = f x₁ .. xₙ` return expression `λ {T} [Space T] a₁ ... aₘ [FunProp xᵢ] : Fun λ t => f x₁ .. (xᵢ t) xₙ` 

where:
  - `Fun`, `FunProp`, `Space` correspond to `funName`, `propName`, `spaceName`
  - `i ∈ argIds`
  - `a₁, ..., aₘ ∈ abstractOver` but any occurance of `xᵢ : X` is replaced with `xᵢ : T → X` 
For example:
```
createFunProp ``differential ``IsSmooth ``Vec (@HAdd.hAdd X X X inst.toHAdd x y) #[4] #[X, inst, x, y]
```
produces
```
∀ {T : Type} [Vec T] {X} [inst : Vec X] (x : X) (y : T → X) [IsSmooth y] : differential λ t => x + (y t)
```
-/
def mkCompositionFunApp (funName propName spaceName : Name) (e : Expr) (argIds : ArraySet Nat) (abstractOver : Array Expr) : MetaM Expr := do

  let args := e.getAppArgs

  let xs := argIds.data.map λ i => args[i]!

  createCompositionOther e xs abstractOver λ T t ys abstractOver e => do

    withLocalDecl `inst .instImplicit (← mkAppM spaceName #[T]) λ SpaceT => do

      let funPropDecls ← ys.mapM λ y => do
        let name := `inst
        let bi := BinderInfo.instImplicit
        let type ← mkAppM propName #[y]
        pure (name, bi, λ _ => pure type)
  
      withLocalDecls funPropDecls λ ysProp => do
        let vars := #[T,SpaceT]
          |>.append abstractOver
          |>.append ysProp
        let statement ← mkAppM funName #[← mkLambdaFVars #[t] e]
        mkForallFVars vars statement

/-- Makes a type that says that `f x₁ .. xₙ` satisfies function propsotion `propName` in `xᵢ`
  
  The returned expression is: `∀ a₁ ... aₘ : FunProp λ xᵢ => f x₁ .. xᵢ xₙ` 
  where `a₁, ..., aₘ ∈ abstractOver` -/
def mkSingleArgFunApp (funName : Name) (e : Expr) (i : Nat) (abstractOver : Array Expr) : MetaM Expr := do

  let args := e.getAppArgs

  let xi := args[i]!

  let statement ← mkAppM funName #[← mkLambdaFVars #[xi] e]

  let abstractOver := abstractOver.filter (λ a => a != xi)

  mkForallFVars abstractOver statement


/--
  Creates argument suffix for a constant and specified arguments.

  Examples:

    For `constName = ``foo` where `foo : ∀ (α : Type) → [inst : Add α] → (x y : α) → α`
    and `argIds = #[2,3]`
    returns `xy` because the third argument has name `x` and the fourth argument has name `y`

    For `HAdd.hAdd : ∀ (α β γ : Type) → [inst : HAdd α β γ] → α → β → γ`
    and `argIds = #[4,5]`
    returns `a4a5` beause fifth and sixth arguments are anonymous
  -/
def constArgSuffix (constName : Name) (argIds : ArraySet Nat) : MetaM String := do

  let info ← getConstInfo constName
  let suffix ← forallTelescope info.type λ args _ => do
    (argIds.data.mapM λ i => do
      let name ← args[i]!.fvarId!.getUserName
      if name.isInternal then
        return name.eraseMacroScopes.appendAfter (toString i)
      else
        return name)

  return suffix.foldl (init:="") λ s n => s ++ toString n


def mkAppFoldrM (const : Name) (xs : Array Expr) : MetaM Expr := do
  if xs.size = 0 then
    return default
  if xs.size = 1 then
    return xs[0]!
  else
    xs[:xs.size-1].foldrM (init:=xs[xs.size-1]!)
      λ x p =>
        mkAppM const #[x,p]

def mkAppFoldlM (const : Name) (xs : Array Expr) : MetaM Expr := do
  if xs.size = 0 then
    return default
  if xs.size = 1 then
    return xs[0]!
  else
    xs[1:].foldlM (init:=xs[0]!)
      λ p x =>
        mkAppM const #[p,x]

/--
For `#[x₁, .., xₙ]` create `(x₁, .., xₙ)`.
-/
def mkProdElem (xs : Array Expr) : MetaM Expr := mkAppFoldrM ``Prod.mk xs

/--
For `(x₀, .., xₙ₋₁)` return `xᵢ` but as a product projection.

For example for `xyz : X × Y × Z`, `mkProdProj xyz 1` returns `xyz.snd.fst`.
-/
def mkProdProj (x : Expr) (i : Nat) : MetaM Expr := do
  let X ← inferType x
  if X.isAppOfArity ``Prod 2 then
     match i with
     | 0 => mkAppM ``Prod.fst #[x]
     | n+1 => mkProdProj (← mkAppM ``Prod.snd #[x]) n
  else
    if i = 0 then
      return x
    else
      throwError "Failed `mkProdProj`, can't take {i}-th element of {← ppExpr x}. It has type {← ppExpr X} which is not a product type!"


def mkProdSplitElem (xs : Expr) (n : Nat) : MetaM (Array Expr) := 
  (Array.mkArray n 0)
    |>.mapIdx (λ i _ => i.1)
    |>.mapM (λ i => mkProdProj xs i)

/--
For free variables `#[x₁, .., xₙ]` create a fitting name for a variable of type `X₁ × .. × Xₙ`

Returns `x₁..xₙ`, for example for `#[x,y]` returns `xy`
 -/
def mkProdFVarName (xs : Array Expr) : MetaM Name := do
  let name : String ← xs.foldlM (init:="") λ n x => do return (n ++ toString (← x.fvarId!.getUserName))
  pure name

def mkUncurryFun (n : Nat) (f : Expr) : MetaM Expr := do
  if n ≤ 1 then
    return f
  forallTelescope (← inferType f) λ xs _ => do
    let ys := xs[0:n]
    let zs := xs[n:]

    let yName ← mkProdFVarName ys
    let yType ← inferType (← mkProdElem ys)

    withLocalDecl yName default yType λ y => do
      let ids := Array.mkArray n 0 |>.mapIdx λ i _ => i.1
      let ys' ← ids.mapM (λ i => mkProdProj y i)
      mkLambdaFVars #[y] (← mkAppM' f ys').headBeta

/--
For expression `e` and free variables `xs = #[x₁, .., xₙ]`
Return 
```
FunProp (uncurryN n λ x₁ .. xₙ => e)
```
 -/
def mkTargetExprFunProp (funProp : Name) (e : Expr) (xs : Array Expr) : MetaM Expr := do

  -- P = FunProp (uncurryN n λ x₁' .. xₙ' => e)
  let P ← 
    mkUncurryFun xs.size (← mkLambdaFVars xs e)
    -- mkAppNoTrailingM ``uncurryN #[nExpr, ← mkLambdaFVars xs e]
    >>=
    λ e' => mkAppM funProp #[e']

  return P


def mkNormalTheoremFunProp (funProp : Name) (e : Expr) (xs : Array Expr) (contextVars : Array Expr) : MetaM Expr := do
  let statement ← mkTargetExprFunProp funProp e xs 

  -- filter out xs from contextVars
  let contextVars := contextVars.filter 
    λ var => 
      if xs.find? (λ x => var == x) |>.isSome then
        false
      else 
        true

  mkForallFVars contextVars statement

def mkCompTheoremFunProp (funProp spaceName : Name) (e : Expr) (xs : Array Expr) (contextVars : Array Expr) : MetaM Expr := do

  createCompositionOther e xs contextVars λ T t ys abstractOver e => do

    withLocalDecl `inst .instImplicit (← mkAppM spaceName #[T]) λ SpaceT => do

      let funPropDecls ← ys.mapM λ y => do
        let name := `inst
        let bi := BinderInfo.instImplicit
        let type ← mkAppM funProp #[y]
        pure (name, bi, λ _ => pure type)
  
      withLocalDecls funPropDecls λ ysProp => do
        let vars := #[T,SpaceT]
          |>.append abstractOver
          |>.append ysProp
        let statement ← mkAppM funProp #[← mkLambdaFVars #[t] e]
        mkForallFVars vars statement


/--
For expression `e = f y₁ .. yₘ` and free variables `xs = #[x₁, .., xₙ]`
Return 
```
λ dx₁ .. dxₙ => ∂ (uncurryN n λ x₁' .. xₙ' => f y₁[xᵢ:=xᵢ'] .. yₘ[xᵢ:=xᵢ']) (x₁, .., xₙ) (dx₁, .., dxₙ)
```
 -/
def mkTargetExprDifferential (e : Expr) (xs : Array Expr) : MetaM Expr := do

  let n := xs.size
  let nExpr := mkNatLit n

  -- f' = ∂ (uncurryN n λ x₁' .. xₙ' => f y₁[xᵢ:=xᵢ'] .. yₘ[xᵢ:=xᵢ'])
  let f' ← 
    mkUncurryFun n (← mkLambdaFVars xs e)
    -- mkAppNoTrailingM ``uncurryN #[nExpr, ← mkLambdaFVars xs e]
    >>=
    λ e' => mkAppM ``differential #[e']

  let dxDecls ← xs.mapM λ x => do
    let id := x.fvarId!
    let name := (← id.getUserName).appendBefore "d"
    let bi ← id.getBinderInfo
    let type ← id.getType
    pure (name, bi, λ _ => pure type)

  withLocalDecls dxDecls λ dxs => do
    
    let xsProd  ← mkProdElem xs
    let dxsProd ← mkProdElem dxs

    mkLambdaFVars dxs (← mkAppM' f' #[xsProd, dxsProd])

/--
For expression `e = f y₁ .. yₘ` and free variables `xs = #[x₁, .., xₙ]`
Return 
```
λ dx₁ .. dxₙ => 𝒯 (uncurryN n λ x₁' .. xₙ' => f y₁[xᵢ:=xᵢ'] .. yₘ[xᵢ:=xᵢ']) (x₁, .., xₙ) (dx₁, .., dxₙ)
```
 -/
def mkTargetExprTangentMap (e : Expr) (xs : Array Expr) : MetaM Expr := do

  let n := xs.size
  let nExpr := mkNatLit n

  -- f' = 𝒯 (uncurryN n λ x₁' .. xₙ' => f y₁[xᵢ:=xᵢ'] .. yₘ[xᵢ:=xᵢ'])
  let f' ← 
    mkUncurryFun n (← mkLambdaFVars xs e)
    -- mkAppNoTrailingM ``uncurryN #[nExpr, ← mkLambdaFVars xs e]
    >>=
    λ e' => mkAppM ``tangentMap #[e']

  let dxDecls ← xs.mapM λ x => do
    let id := x.fvarId!
    let name := (← id.getUserName).appendBefore "d"
    let bi ← id.getBinderInfo
    let type ← id.getType
    pure (name, bi, λ _ => pure type)

  withLocalDecls dxDecls λ dxs => do
    
    let xsProd  ← mkProdElem xs
    let dxsProd ← mkProdElem dxs

    mkLambdaFVars dxs (← mkAppM' f' #[xsProd, dxsProd])


/--
For expression `e = f y₁ .. yₘ` and free variables `xs = #[x₁, .., xₙ]`
Return 
```
λ (xs' : X₁ × .. Xₙ) => (uncurryN n λ x₁' .. xₙ' => f y₁[xᵢ:=xᵢ'] .. yₘ[xᵢ:=xᵢ'])† xs'
```
where `xᵢ : Xᵢ`
 -/
def mkTargetExprAdjoint (e : Expr) (xs : Array Expr) : MetaM Expr := do
  
  let n := xs.size
  let nExpr := mkNatLit n

  -- f' = (uncurryN n λ x₁' .. xₙ' => f y₁[xᵢ:=xᵢ'] .. yₘ[xᵢ:=xᵢ'])†
  let f' ← 
    mkUncurryFun n (← mkLambdaFVars xs e)
    >>=
    λ e' => mkAppM ``adjoint #[e']
  
  let xsProdName := (← mkProdFVarName xs).appendAfter "'"
  let bi : BinderInfo := default
  let xsProdType ← inferType e --(← mkProdElem xs)

  withLocalDecl xsProdName bi xsProdType λ xsProd => do

    mkLambdaFVars #[xsProd] (← mkAppM' f' #[xsProd])


/--
For expression `e = f y₁ .. yₘ` and free variables `xs = #[x₁, .., xₙ]`
Return 
```
λ (dxs' : X₁ × .. Xₙ) => ∂† (uncurryN n λ x₁' .. xₙ' => f y₁[xᵢ:=xᵢ'] .. yₘ[xᵢ:=xᵢ'])† (x₁, .., xₙ) dxs'
```
where `xᵢ : Xᵢ`
 -/
def mkTargetExprAdjDiff (e : Expr) (xs : Array Expr) : MetaM Expr := do
  
  let n := xs.size
  let nExpr := mkNatLit n

  -- f' = ∂† (uncurryN n λ x₁' .. xₙ' => f y₁[xᵢ:=xᵢ'] .. yₘ[xᵢ:=xᵢ'])
  let f' ← 
    mkUncurryFun n (← mkLambdaFVars xs e)
    >>=
    λ e' => mkAppM ``adjointDifferential #[e']
  
  let dxsName := (← mkProdFVarName xs).appendBefore "d" |>.appendAfter "'"
  let bi : BinderInfo := .default
  let dxsType ← inferType e

  withLocalDecl dxsName bi dxsType λ dxs => do

    let xsProd  ← mkProdElem xs

    mkLambdaFVars #[dxs] (← mkAppM' f' #[xsProd, dxs])


/--
For expression `e = f y₁ .. yₘ` and free variables `xs = #[x₁, .., xₙ]`
Return 
```
ℛ (uncurryN n λ x₁' .. xₙ' => f y₁[xᵢ:=xᵢ'] .. yₘ[xᵢ:=xᵢ'])† (x₁, .., xₙ)'
```
 -/
def mkTargetExprRevDiff (e : Expr) (xs : Array Expr) : MetaM Expr := do
  
  let n := xs.size
  let nExpr := mkNatLit n

  -- f' = ℛ (uncurryN n λ x₁' .. xₙ' => f y₁[xᵢ:=xᵢ'] .. yₘ[xᵢ:=xᵢ'])
  let f' ← 
    mkUncurryFun n (← mkLambdaFVars xs e)
    >>=
    λ e' => mkAppM ``reverseDifferential #[e']
  
  let xsProd  ← mkProdElem xs

  mkAppM' f' #[xsProd]

/--
Applies function transformation to `λ x₁ .. xₙ => e` w.r.t. to all the free variables `xs = #[x₁, .., xₙ]`
-/
def mkTargetExpr (transName : Name) (e : Expr) (xs : Array Expr) : MetaM Expr := do
  if transName == ``differential then
    mkTargetExprDifferential e xs
  else if transName == ``tangentMap then
    mkTargetExprTangentMap e xs
  else if transName == ``adjoint then
    mkTargetExprAdjoint e xs
  else if transName == ``adjointDifferential then
    mkTargetExprAdjDiff e xs
  else if transName == ``reverseDifferential then
    mkTargetExprRevDiff e xs
  else
    throwError "Error in `mkTargetExpr`, unrecognized function transformation `{transName}`."


def mkNormalTheoremRhsType (transName : Name) (e : Expr) (xs : Array Expr) : MetaM Expr :=
  mkTargetExpr transName e xs >>= inferType


def maybeFilterContextVars (transName : Name) (xs : Array Expr) (contextVars : Array Expr) : Array Expr :=
  if transName == ``adjoint then
    contextVars.filter 
      λ var => 
        if xs.find? (λ x => var == x) |>.isSome then
          false
        else 
          true
    else
      contextVars

def mkNormalTheorem (transName : Name) (e : Expr) (xs : Array Expr) (contextVars : Array Expr) (defVal : Expr) : MetaM Expr := do

  let lhs ← mkTargetExpr transName e xs 

  let contextVars := maybeFilterContextVars transName xs contextVars

  lambdaTelescope lhs λ xs lhs => do

    let statement ← mkEq lhs (← mkAppM' defVal xs).headBeta

    mkForallFVars (contextVars.append xs) statement

/--
This function expects that `defVal` has the same type as `mkTargetExprDifferential e xs`

Assuming that `xs` is a subset of `contextVars`
-/
def mkCompTheoremDifferential (e : Expr) (xs : Array Expr) (contextVars : Array Expr) (defVal : Expr) : MetaM Expr := do

  createCompositionOther e xs contextVars λ T t ys contextVars e => do

    withLocalDecl `inst .instImplicit (← mkAppM ``Vec #[T]) λ SpaceT => do
      let dtName := (← t.fvarId!.getUserName).appendBefore "d"
      withLocalDecl dtName .default (← inferType t) λ dt => do

        let funPropDecls ← ys.mapM λ y => do
          let name := `inst
          let bi := BinderInfo.instImplicit
          let type ← mkAppM ``IsSmooth #[y]
          pure (name, bi, λ _ => pure type)

        withLocalDecls funPropDecls λ ysProp => do
          let contextVars := #[T,SpaceT]
            |>.append contextVars
            |>.append ysProp

          let lhs ← mkAppM ``differential #[← mkLambdaFVars #[t] e]

          let mut lctx ← getLCtx
          let mut i := lctx.numIndices
          let mut xs'  : Array Expr := .mkEmpty xs.size
          let mut dxs' : Array Expr := .mkEmpty xs.size
          for y in ys do 
            let id := y.fvarId!
            let  xName := (← id.getUserName).appendAfter "'"
            let dxName := xName.appendBefore "d"
            let  xVal ← mkAppM' y #[t]
            let dxVal ← mkAppM' (← mkAppM ``differential #[y]) #[t,dt]
            let  xType ← inferType xVal
            let dxType ← inferType dxVal
            let  xId ← mkFreshFVarId
            let dxId ← mkFreshFVarId
            xs'  :=  xs'.push (mkFVar  xId)
            dxs' := dxs'.push (mkFVar dxId)
            lctx := lctx.addDecl (mkLetDeclEx i xId xName xType xVal)
            lctx := lctx.addDecl (mkLetDeclEx (i+1) dxId dxName dxType dxVal)
            i := i + 2

          withLCtx lctx (← getLocalInstances) do

            let rhs ← 
              mkLambdaFVars xs defVal -- abstract old xs
              >>=
              λ e => mkAppM' e xs' >>= pure ∘ Expr.headBeta  -- replace xs with xs' 
              >>=
              λ e => mkAppM' e dxs' >>= pure ∘ Expr.headBeta -- apply dxs'
              >>=
              λ e => mkLambdaFVars (xs'.append dxs') e
              >>=
              λ e => mkLambdaFVars #[t,dt] e  -- abstract over t and dt

            mkForallFVars contextVars (← mkEq lhs rhs)


/--
This function expects that `defVal` has the same type as `mkTargetExprTangentMap e xs`

Assuming that `xs` is a subset of `contextVars`
-/
def mkCompTheoremTangentMap (e : Expr) (xs : Array Expr) (contextVars : Array Expr) (defVal : Expr) : MetaM Expr := do

  createCompositionOther e xs contextVars λ T t ys contextVars e => do

    withLocalDecl `inst .instImplicit (← mkAppM ``Vec #[T]) λ SpaceT => do
      let dtName := (← t.fvarId!.getUserName).appendBefore "d"
      withLocalDecl dtName .default (← inferType t) λ dt => do

        let funPropDecls ← ys.mapM λ y => do
          let name := `inst
          let bi := BinderInfo.instImplicit
          let type ← mkAppM ``IsSmooth #[y]
          pure (name, bi, λ _ => pure type)

        withLocalDecls funPropDecls λ ysProp => do
          let contextVars := #[T,SpaceT]
            |>.append contextVars
            |>.append ysProp

          let lhs ← mkAppM ``tangentMap #[← mkLambdaFVars #[t] e]

          let mut lctx ← getLCtx
          let mut i := lctx.numIndices
          let mut Txs' : Array Expr := .mkEmpty xs.size
          for y in ys do 
            let id := y.fvarId!
            let  xName := (← id.getUserName).appendAfter "'"
            let TxName := xName.appendBefore "T"
            let TxVal ← mkAppM' (← mkAppM ``tangentMap #[y]) #[t,dt]
            let TxType ← inferType TxVal
            let TxId ← mkFreshFVarId
            let TxFVar := mkFVar TxId
            Txs'  :=  Txs'.push (mkFVar TxId)
            lctx := lctx.addDecl (mkLetDeclEx i TxId TxName TxType TxVal)
            i := i + 1

          withLCtx lctx (← getLocalInstances) do

            let  xs' ← Txs'.mapM (λ Tx => mkProdProj Tx 0)
            let dxs' ← Txs'.mapM (λ Tx => mkProdProj Tx 1)

            let rhs ← do
              let mut e ← mkLambdaFVars xs defVal -- abstract old xs
              e ← mkAppM' e xs' >>= pure ∘ Expr.headBeta  -- replace xs with xs' 
              e ← mkAppM' e dxs' >>= pure ∘ Expr.headBeta -- apply dxs'
              e ← mkLambdaFVars Txs' e
              mkLambdaFVars #[t,dt] e  -- abstract over t and dt

            mkForallFVars contextVars (← mkEq lhs rhs)


/--
This function expects that `defVal` has the same type as `mkTargetExprTangentMap e xs`

Assuming that `xs` is a subset of `contextVars`
-/
def mkCompTheoremAdjoint (e : Expr) (xs : Array Expr) (contextVars : Array Expr) (defVal : Expr) : MetaM Expr := do

  createCompositionOther e xs contextVars λ T t ys contextVars e => do

    withLocalDecl `inst .instImplicit (← mkAppM ``SemiHilbert #[T]) λ SpaceT => do
      let xName' := (← mkProdFVarName xs).appendAfter "'"
      let xType' ← inferType e
      withLocalDecl xName' .default xType' λ x' => do

        let funPropDecls ← ys.mapM λ y => do
          let name := `inst
          let bi := BinderInfo.instImplicit
          let type ← mkAppM ``HasAdjoint #[y]
          pure (name, bi, λ _ => pure type)

        withLocalDecls funPropDecls λ ysProp => do
          let contextVars := #[T,SpaceT]
            |>.append contextVars
            |>.append ysProp

          let lhs ← mkAppM ``adjoint #[← mkLambdaFVars #[t] e]
            
          let xName'' := xName'.appendAfter "'"
          let xVal'' := (← mkAppM' defVal #[x']).headBeta
          let xType'' ← inferType xVal''

          withLetDecl xName'' xType'' xVal'' λ x'' => do

            let yVals' ← ys.mapIdxM λ i y => do
                let y ← mkAppM ``adjoint #[y] 
                mkAppM' y #[← mkProdProj x'' i]

            let ySum ← mkAppFoldlM ``HAdd.hAdd yVals'

            let rhs ← mkLambdaFVars #[x',x''] ySum

            mkForallFVars contextVars (← mkEq lhs rhs)


/--
This function expects that `defVal` has the same type as `mkTargetExprDifferential e xs`

Assuming that `xs` is a subset of `contextVars`
-/
def mkCompTheoremAdjDiff (e : Expr) (xs : Array Expr) (contextVars : Array Expr) (defVal : Expr) : MetaM Expr := do

  createCompositionOther e xs contextVars λ T t ys contextVars e => do

    withLocalDecl `inst .instImplicit (← mkAppM ``SemiHilbert #[T]) λ SpaceT => do

      let dxsName' := (← mkProdFVarName xs).appendAfter "'" |>.appendBefore "d"
      let dxsType' ← inferType e

      withLocalDecl dxsName' .default dxsType' λ dxs' => do

        let funPropDecls ← ys.mapM λ y => do
          let name := `inst
          let bi := BinderInfo.instImplicit
          let type ← mkAppM ``HasAdjDiff #[y]
          pure (name, bi, λ _ => pure type)

        withLocalDecls funPropDecls λ ysProp => do
          let contextVars := #[T,SpaceT]
            |>.append contextVars
            |>.append ysProp

          let lhs ← mkAppM ``adjointDifferential #[← mkLambdaFVars #[t] e]

          let mut lctx ← getLCtx
          let mut i := lctx.numIndices
          let mut xs'  : Array Expr := .mkEmpty xs.size
          for y in ys do 
            let id := y.fvarId!
            let  xName := (← id.getUserName).appendAfter "'"
            let  xVal ← mkAppM' y #[t]
            let  xType ← inferType xVal
            let  xId ← mkFreshFVarId
            xs'  :=  xs'.push (mkFVar  xId)
            lctx := lctx.addDecl (mkLetDeclEx i xId xName xType xVal)
            i := i + 1

          withLCtx lctx (← getLocalInstances) do

            -- replace `xs` with `xs'`
            let defVal := (← mkAppM' (← mkLambdaFVars xs defVal) xs').headBeta

            let dxsName : Name := ← xs.foldlM (init:="") λ (s : String) x => do
              let xName := toString (← x.fvarId!.getUserName)
              return s ++ "d" ++ xName
            let dxsVal := (← mkAppM' defVal #[dxs']).headBeta
            let dxsType ← inferType dxsVal

            withLetDecl dxsName dxsType dxsVal λ dxs => do

              let dxVals ← mkProdSplitElem dxs xs.size

              let xdxVals ← (ys.zip dxVals).mapM 
                λ (y,dx) => mkAppM ``adjointDifferential #[y, t, dx]

              let sum ← mkAppFoldlM ``HAdd.hAdd xdxVals

              let rhs ← mkLambdaFVars ((#[t,dxs'].append xs').push dxs) sum

              mkForallFVars contextVars (← mkEq lhs rhs)

/--
This function expects that `defVal` has the same type as `mkTargetExprDifferential e xs`

Assuming that `xs` is a subset of `contextVars`
-/
def mkCompTheoremRevDiff (e : Expr) (xs : Array Expr) (contextVars : Array Expr) (defVal : Expr) : MetaM Expr := do

  createCompositionOther e xs contextVars λ T t ys contextVars e => do

    withLocalDecl `inst .instImplicit (← mkAppM ``SemiHilbert #[T]) λ SpaceT => do

      let funPropDecls ← ys.mapM λ y => do
        let name := `inst
        let bi := BinderInfo.instImplicit
        let type ← mkAppM ``HasAdjDiff #[y]
        pure (name, bi, λ _ => pure type)

      withLocalDecls funPropDecls λ ysProp => do
        let contextVars := #[T,SpaceT]
          |>.append contextVars
          |>.append ysProp

        let lhs ← mkAppM ``reverseDifferential #[← mkLambdaFVars #[t] e]

        let mut lctx ← getLCtx
        let mut i := lctx.numIndices
        let mut Rxs : Array Expr := .mkEmpty xs.size
        for y in ys do 
          let id := y.fvarId!
          let RxName := (← id.getUserName).appendBefore "R"
          let RxVal ← mkAppM ``reverseDifferential #[y, t]
          let RxType ← inferType RxVal
          let RxId ← mkFreshFVarId
          Rxs  := Rxs.push (mkFVar RxId)
          lctx := lctx.addDecl (mkLetDeclEx i RxId RxName RxType RxVal)
          i := i + 1

        withLCtx lctx (← getLocalInstances) do

          let xs' ← Rxs.mapM λ Rx => mkProdProj Rx 0

          -- replace `xs` with `xs'`
          let RfxVal := (← mkAppM' (← mkLambdaFVars xs defVal) xs').headBeta

          withLetDecl `Rfx (← inferType RfxVal) RfxVal λ Rfx => do

            let fx  ← mkProdProj Rfx 0
            let df' ← mkProdProj Rfx 1

            let dxsName' := (← mkProdFVarName xs).appendAfter "'" |>.appendBefore "d"
            let dxsType' ← inferType e

            let dF' ←
              withLocalDecl dxsName' .default dxsType' λ dxs' => do

                let dxsName : Name := ← xs.foldlM (init:="") λ (s : String) x => do
                  let xName := toString (← x.fvarId!.getUserName)
                  return s ++ "d" ++ xName
                let dxsVal ← mkAppM' df' #[dxs']
                let dxsType ← inferType dxsVal

                withLetDecl dxsName dxsType dxsVal λ dxs => do

                  let dxVals ← mkProdSplitElem dxs xs.size
                  let dxFuns ← Rxs.mapM λ Rx => mkProdProj Rx 1

                  let xdxVals ← (dxFuns.zip dxVals).mapM 
                    λ (df,dx) => mkAppM' df #[dx]

                  let sum ← mkAppFoldlM ``HAdd.hAdd xdxVals

                  mkLambdaFVars #[dxs',dxs] sum

            let rhs ← mkLambdaFVars ((#[t].append Rxs).push Rfx) (← mkProdElem #[fx, dF'])

            mkForallFVars contextVars (← mkEq lhs rhs)



def mkCompTheorem (transName : Name) (e : Expr) (xs : Array Expr) (contextVars : Array Expr) (defVal : Expr) : MetaM Expr := do
  if transName == ``differential then
    mkCompTheoremDifferential e xs contextVars defVal
  else if transName == ``tangentMap then
    mkCompTheoremTangentMap e xs contextVars defVal
  else if transName == ``adjoint then
    mkCompTheoremAdjoint e xs contextVars defVal
  else if transName == ``adjointDifferential then
    mkCompTheoremAdjDiff e xs contextVars defVal
  else if transName == ``reverseDifferential then
    mkCompTheoremRevDiff e xs contextVars defVal
  else
    throwError "Error in `mkCompTheorem`, unrecognized function transformation `{transName}`."


def _root_.Lean.TSyntax.argSpecNames (argSpec : TSyntax ``argSpec) : Array Name := 
  match argSpec with 
  | `(argSpec| $id:ident) => #[id.getId]
  | `(argSpec| ($id:ident, $ids:ident,*)) => #[id.getId].append (ids.getElems.map λ id => id.getId)
  | _ => #[]

syntax "funProp" ident ident bracketedBinder* ":=" term : argProp
syntax "funTrans" ident bracketedBinder* ":=" term "by" tacticSeq "by" tacticSeq : argProp

elab_rules : command
| `(function_property $id $parms* $[: $retType:term]? 
    argument $argSpec $assumptions1*
    funProp $propId $spaceId $assumptions2* := $proof) => do

  Command.liftTermElabM  do

    Term.elabBinders (parms |>.append assumptions1 |>.append assumptions2) λ contextVars => do

      let propName := propId.getId
      let spaceName := spaceId.getId
  
      let argNames : Array Name := argSpec.argSpecNames 

      let explicitArgs := (← contextVars.filterM λ x => do pure (← x.fvarId!.getBinderInfo).isExplicit)
      let e ← mkAppM id.getId explicitArgs
      let args := e.getAppArgs

      let mainArgIds ← argNames.mapM λ name => do
        let idx? ← args.findIdxM? (λ arg => do
          if let .some fvar := arg.fvarId? then
            let name' ← fvar.getUserName
            pure (name' == name)
          else 
            pure false)
        match idx? with
        | some idx => pure idx
        | none => throwError "Specified argument `{name}` is not valid!"

      let xs := mainArgIds.map λ i => args[i]!
      let mainArgIds := mainArgIds.toArraySet

      -- normal theorem - in the form `FunProp (uncurryN n λ x₁ .. xₙ => e)`
      let normalTheorem ← mkNormalTheoremFunProp propName e xs contextVars >>= instantiateMVars

      let prf ← forallTelescope normalTheorem λ ys b => do
        let val ← Term.elabTermAndSynthesize proof b 
        mkLambdaFVars ys val

      let theoremName := id.getId
        |>.append `arg_
        |>.appendAfter (← constArgSuffix id.getId mainArgIds)
        |>.append propName.getString

      let info : TheoremVal :=
      {
        name := theoremName
        type := normalTheorem
        value := prf
        levelParams := []
      }

      addDecl (.thmDecl info)
      addInstance info.name .local 1000

      -- composition theorem - in the form `FunProp (λ t => e[xᵢ:=yᵢ t])`
      let compTheorem   ← mkCompTheoremFunProp propName spaceName e xs contextVars >>= instantiateMVars

      let compTheoremName := theoremName.appendAfter "'"

      let prf ← forallTelescope compTheorem λ ys b => do
        -- TODO: Fill the proof here!!! 
        -- I think I can manually apply composition rule and then it should be 
        -- automatically discargable by using the normal theorem and product rule
        let val ← Term.elabTermAndSynthesize (← `(by sorry)) b  
        mkLambdaFVars ys val

      let info : TheoremVal :=
      {
        name := compTheoremName
        type := compTheorem
        value := prf
        levelParams := []
      }

      addDecl (.thmDecl info)
      addInstance info.name .local 1000

      addFunctionTheorem id.getId propName mainArgIds ⟨theoremName, compTheoremName⟩

elab_rules : command
| `(function_property $id $parms* $[: $retType]? 
    argument $argSpec $assumptions1*
    funTrans $transId $assumptions2* := $Tf by $proof by $proof2) => do

  Command.liftTermElabM  do

    Term.elabBinders (parms |>.append assumptions1 |>.append assumptions2) λ contextVars => do

      let transName := transId.getId
  
      let argNames : Array Name := argSpec.argSpecNames 

      let explicitArgs := (← contextVars.filterM λ x => do pure (← x.fvarId!.getBinderInfo).isExplicit)
      let e ← mkAppM id.getId explicitArgs
      let args := e.getAppArgs

      let mainArgIds ← argNames.mapM λ name => do
        let idx? ← args.findIdxM? (λ arg => do
          if let .some fvar := arg.fvarId? then
            let name' ← fvar.getUserName
            pure (name' == name)
          else 
            pure false)
        match idx? with
        | some idx => pure idx
        | none => throwError "Specified argument `{name}` is not valid!"

      let xs := mainArgIds.map λ i => args[i]!
      let mainArgIds := mainArgIds.toArraySet

      -- make definition
      let defType ← inferType (← mkTargetExpr transName e xs)
      let defVal  ← Term.elabTermAndSynthesize Tf defType

      let defName := id.getId
        |>.append "arg_"
        |>.appendAfter (← constArgSuffix id.getId mainArgIds)
        |>.append transName.getString

      let defValLambda ← do
        let contextVars := maybeFilterContextVars transName xs contextVars
        mkLambdaFVars contextVars defVal >>= instantiateMVars

      let info : DefinitionVal := 
      {
        name := defName
        type := ← inferType defValLambda
        value := defValLambda
        hints := .regular 0
        safety := .safe
        levelParams := []
      }

      addDecl (.defnDecl info)

      let normalTheorem ← mkNormalTheorem transName e xs contextVars defVal >>= instantiateMVars

      IO.println s!"Normal theorem for {transName}:\n{← ppExpr normalTheorem}"

      let prf ← forallTelescope normalTheorem λ contextVars statement => do
        let prf ← Term.elabTermAndSynthesize (← `(by $proof)) statement
        mkLambdaFVars contextVars prf


      let theoremName := defName.appendAfter "_simp"

      let info : TheoremVal :=
      {
        name := theoremName
        type := normalTheorem
        value := prf
        levelParams := []
      }

      addDecl (.thmDecl info)

      dbg_trace "Starting to work composition theorem"

      let compTheorem ← mkCompTheorem transName e xs contextVars defVal >>= instantiateMVars

      IO.println s!"Composition theorem for {transName}:\n{← ppExpr compTheorem}"

      let prf ← forallTelescope compTheorem λ contextVars statement => do
        let prf ← Term.elabTermAndSynthesize (← `(by $proof2)) statement
        mkLambdaFVars contextVars prf

      let compTheoremName := defName.appendAfter "_simp'"

      let info : TheoremVal :=
      {
        name := compTheoremName
        type := compTheorem
        value := prf
        levelParams := []
      }

      addDecl (.thmDecl info)

      addFunctionTheorem id.getId transName mainArgIds ⟨theoremName,compTheoremName⟩


 
instance {X} [Vec X] : IsSmooth (λ x : X => x) := sorry
instance {X Y} [Vec X] [Vec Y] (x : X): IsSmooth (λ y : Y => x) := sorry
instance {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : Y → Z) (g : X → Y) [IsSmooth f] [IsSmooth g] : IsSmooth (λ x  => f (g x)) := sorry
instance {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : X → Y) (g : X → Z) [IsSmooth f] [IsSmooth g] : IsSmooth (λ x  => (f x, g x)) := sorry

instance {X Y Z} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] (f : Y → Z) (g : X → Y) [HasAdjoint f] [HasAdjoint g] : HasAdjoint (λ x  => f (g x)) := sorry
instance {X Y Z} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] (f : X → Y) (g : X → Z) [HasAdjoint f] [HasAdjoint g] : HasAdjoint (λ x  => (f x, g x)) := sorry


instance {X Y} [Vec X] [Vec Y] (x : X): IsSmooth (λ xy : X×Y => xy.1) := sorry
instance {X Y} [Vec X] [Vec Y] (x : X): IsSmooth (λ xy : X×Y => xy.2) := sorry

@[simp]
theorem diff_id {X} [Vec X] 
  : ∂ (λ x : X => x) 
    =
    λ x dx => dx := sorry

@[simp]
theorem diff_const {X} [Vec X] (x : X)
  : ∂ (λ y : Y => x) 
    =
    λ y dy => 0 := sorry

@[simp]
theorem diff_comp {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : Y → Z) (g : X → Y) [IsSmooth f] [IsSmooth g]
  : ∂ (λ x => f (g x)) 
    =
    λ x dx => ∂ f (g x) (∂ g x dx) := sorry

@[simp]
theorem tangentMap_comp {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : Y → Z) (g : X → Y) [IsSmooth f] [IsSmooth g]
  : 𝒯 (λ x => f (g x)) 
    =
    λ x dx => 
      let (y,dy) := 𝒯 g x dx 
      𝒯 f y dy 
  := sorry

@[simp]
theorem adjoint_comp {X Y Z} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] (f : Y → Z) (g : X → Y) [HasAdjoint f] [HasAdjoint g]
  : (λ x => f (g x))†
    =
    λ z => g† (f† z)
  := sorry


@[simp]
theorem diff_prodMk {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : X → Y) (g : X → Z) [IsSmooth f] [IsSmooth g]
  : ∂ (λ x => (f x, g x)) 
    =
    λ x dx => (∂ f x dx, ∂ g x dx) := sorry

@[simp]
theorem tangentMap_prodMk {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : X → Y) (g : X → Z) [IsSmooth f] [IsSmooth g]
  : 𝒯 (λ x => (f x, g x)) 
    =
    λ x dx => 
      let (y,dy) := 𝒯 f x dx
      let (z,dz) := 𝒯 g x dx
      ((y,z), (dy,dz)) := sorry

@[simp]
theorem adjoint_prodMk {X Y Z} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] (f : X → Y) (g : X → Z) [HasAdjoint f] [HasAdjoint g]
  : (λ x => (f x, g x))†
    =
    λ (y,z) => 
      f† y + g† z := sorry


instance {X} [SemiHilbert X] : HasAdjDiff (λ x : X => x) := sorry
instance {X Y} [SemiHilbert X] [SemiHilbert Y] (x : X): HasAdjDiff (λ y : Y => x) := sorry

theorem isLin_isSmooth {X Y} [Vec X] [Vec Y] {f : X → Y} [inst : IsLin f] : IsSmooth f := inst.isSmooth
theorem hasAdjoint_on_FinVec {X Y ι κ} {_ : Enumtype ι} {_ : Enumtype κ} [FinVec X ι] [FinVec Y κ] {f : X → Y} [inst : IsLin f] : HasAdjoint f := sorry
theorem hasAdjDiff_on_FinVec {X Y ι κ} {_ : Enumtype ι} {_ : Enumtype κ} [FinVec X ι] [FinVec Y κ] {f : X → Y} [inst : IsSmooth f] : HasAdjDiff f := sorry


syntax " IsSmooth " bracketedBinder* (":=" term)? : argProp

macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $argSpec:argSpec $assumptions1*
    IsSmooth $assumptions2* $[:= $proof]?) => do
  let prop : Ident := mkIdent ``IsSmooth
  let space : Ident := mkIdent ``Vec
  let prf := proof.getD (← `(term| by first | (unfold $id; infer_instance) | infer_instance))
  `(function_property $id $parms* $[: $retType:term]? 
    argument $argSpec $assumptions1*
    funProp $prop $space $assumptions2* := $prf)


syntax " IsLin " bracketedBinder* (":=" term)? : argProp

macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $argSpec:argSpec  $assumptions1*
    IsLin $extraAssumptions* $[:= $proof]?) => do
  let prop : Ident := mkIdent ``IsLin
  let space : Ident := mkIdent ``Vec
  let prf := proof.getD (← `(term| by first | (unfold $id; infer_instance) | infer_instance))
  `(function_property $id $parms* $[: $retType:term]? 
    argument $argSpec  $assumptions1*
    funProp $prop $space $extraAssumptions* := $prf)


syntax " HasAdjoint " bracketedBinder* (":=" term)? : argProp

macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $argSpec:argSpec  $assumptions1*
    HasAdjoint $extraAssumptions* $[:= $proof]?) => do
  let prop : Ident := mkIdent ``HasAdjoint
  let space : Ident := mkIdent ``SemiHilbert
  let prf := proof.getD (← `(term| by first | (unfold $id; infer_instance) | infer_instance))
  `(function_property $id $parms* $[: $retType:term]? 
    argument $argSpec  $assumptions1*
    funProp $prop $space $extraAssumptions* := $prf)


syntax " HasAdjDiff " bracketedBinder* (":=" term)? : argProp

macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $argSpec:argSpec  $assumptions1*
    HasAdjDiff $extraAssumptions* $[:= $proof]?) => do
  let prop : Ident := mkIdent ``HasAdjDiff
  let space : Ident := mkIdent ``SemiHilbert
  let prf := proof.getD (← `(term| by first | (unfold $id; infer_instance) | infer_instance))
  `(function_property $id $parms* $[: $retType:term]? 
    argument $argSpec  $assumptions1*
    funProp $prop $space $extraAssumptions* := $prf)

#check Eq.trans
#check uncurryN

function_properties HAdd.hAdd {X : Type} (x y : X) : X
argument (x,y) [Vec X]
  IsLin    := sorry,
  IsSmooth := by apply isLin_isSmooth,
  funTrans SciLean.differential := λ dx dy => dx + dy by sorry 
  by
    simp only
      [diff_comp (λ xy : X×X => xy.fst + xy.snd) (λ t => (x t, y t)),
       HAdd.hAdd.arg_a4a5.differential_simp,
       diff_prodMk]
    done,
  funTrans SciLean.tangentMap := λ dx dy => (x + y, dx + dy)  by sorry 
  by 
    simp [tangentMap_comp (λ xy : X×X => xy.fst + xy.snd) (λ t => (x t, y t))]
    simp [HAdd.hAdd.arg_a4a5.tangentMap_simp]
    done
argument (x,y) [SemiHilbert X]
  HasAdjoint := sorry,
  HasAdjDiff := sorry,
  funTrans SciLean.adjoint := λ xy' => (xy', xy')  by sorry 
  by 
    simp [adjoint_comp (λ xy : X×X => xy.fst + xy.snd) (λ t => (x t, y t))]
    simp [HAdd.hAdd.arg_a4a5.adjoint_simp]
    done,
  funTrans SciLean.adjointDifferential := λ xy' => (xy', xy')  by sorry by sorry
argument x
  IsSmooth [Vec X] := by infer_instance,
  HasAdjDiff [SemiHilbert X] := by infer_instance,
  funTrans SciLean.differential [Vec X] := λ dx => dx by
    simp [HAdd.hAdd.arg_a4a5.differential_simp']
    done
  by
    sorry,
  funTrans SciLean.tangentMap [Vec X] := λ dx => (x+y, dx) by 
    simp [HAdd.hAdd.arg_a4a5.differential_simp', tangentMap]
    done
  by
    sorry
argument y
  IsSmooth [Vec X] := by apply HAdd.hAdd.arg_a4a5.IsSmooth',
  HasAdjDiff [SemiHilbert X] := by apply HAdd.hAdd.arg_a4a5.HasAdjDiff',
  funTrans SciLean.differential [Vec X] := λ dy => dy by 
    rw [HAdd.hAdd.arg_a4a5.differential_simp']; simp
    done
  by
    sorry

#check HAdd.hAdd.arg_a5.differential_simp


example {X} [Vec X] (y : X) : IsSmooth λ x : X => x + y := by infer_instance
example {X} [Vec X] (y : X) : IsSmooth λ x : X => y + x := by infer_instance

#check HAdd.hAdd.arg_a4a5.IsSmooth

#check HAdd.hAdd.arg_a4a5.differential
#check HAdd.hAdd.arg_a4a5.differential_simp
#check HAdd.hAdd.arg_a4a5.differential_simp'
#check HAdd.hAdd.arg_a4a5.tangentMap
#check HAdd.hAdd.arg_a4a5.tangentMap_simp
#check HAdd.hAdd.arg_a4a5.tangentMap_simp'

#check HAdd.hAdd.arg_a4.IsSmooth
#check HAdd.hAdd.arg_a5.IsSmooth'
#check HAdd.hAdd.arg_a5.differential_simp


def foo {α β γ : Type} (a : α) (b : β) (c : γ) : γ := sorry


function_properties SciLean.foo {α β γ : Type} (a : α) (b : β) (c : γ)
argument (a,c) [Vec α] [Vec γ]
  IsLin := sorry,
  IsSmooth := isLin_isSmooth,
  funTrans SciLean.differential := sorry by sorry by sorry,
  funTrans SciLean.tangentMap := sorry by sorry by sorry
argument (a,c) [SemiHilbert α] [SemiHilbert γ]
  HasAdjoint := sorry,
  HasAdjDiff := sorry,
  funTrans SciLean.adjoint := sorry  by sorry by sorry,
  funTrans SciLean.adjointDifferential := sorry  by sorry by sorry,
  funTrans SciLean.reverseDifferential := sorry  by sorry by sorry
argument (a,b,c) [SemiHilbert α] [SemiHilbert β] [SemiHilbert γ]
  HasAdjoint := sorry,
  HasAdjDiff := sorry,
  funTrans SciLean.adjoint := λ c => (0,0,c) by sorry 
  by 
    simp only 
         [adjoint_comp (λ abc : α×β×γ => foo abc.1 abc.2.1 abc.2.2) (λ t => (a t, b t, c t)),
          adjoint_prodMk,
          foo.arg_abc.adjoint_simp,
          add_assoc]
    done,
  funTrans SciLean.adjointDifferential := sorry  by sorry by sorry,
  funTrans SciLean.reverseDifferential := sorry  by sorry by sorry

#check foo.arg_ac.adjoint
#check foo.arg_ac.adjointDifferential


#eval printFunctionTheorems
