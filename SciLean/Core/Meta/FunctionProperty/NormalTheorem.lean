import SciLean.Core.Defs
import SciLean.Lean.Meta.Basic

namespace SciLean

set_option linter.unusedVariables false 

open Lean Parser.Term Lean.Elab Meta

/--
For free variables `#[x₁, .., xₙ]` create a fitting name for a variable of type `X₁ × .. × Xₙ`

Returns `x₁..xₙ`, for example for `#[x,y]` returns `xy`
 -/
private def mkProdFVarName (xs : Array Expr) : MetaM Name := do
  let name : String ← xs.foldlM (init:="") λ n x => do return (n ++ toString (← x.fvarId!.getUserName))
  pure name


/--
For expression `e` and free variables `xs = #[x₁, .., xₙ]`
Return 
```
FunProp (uncurryN n λ x₁ .. xₙ => e)
```
 -/
def mkNormalTheoremLhsFunProp (funProp : Name) (e : Expr) (xs : Array Expr) : MetaM Expr := do

  -- P = FunProp (uncurryN n λ x₁' .. xₙ' => e)
  let P ← 
    mkUncurryFun xs.size (← mkLambdaFVars xs e)
    -- mkAppNoTrailingM ``uncurryN #[nExpr, ← mkLambdaFVars xs e]
    >>=
    λ e' => mkAppM funProp #[e']

  return P


def mkNormalTheoremFunProp (funProp : Name) (e : Expr) (xs : Array Expr) (contextVars : Array Expr) : MetaM Expr := do
  let statement ← mkNormalTheoremLhsFunProp funProp e xs 

  -- filter out xs from contextVars
  let contextVars := contextVars.filter 
    λ var => 
      if xs.find? (λ x => var == x) |>.isSome then
        false
      else 
        true

  mkForallFVars contextVars statement >>= instantiateMVars


/--
For expression `e = f y₁ .. yₘ` and free variables `xs = #[x₁, .., xₙ]`
Return 
```
λ dx₁ .. dxₙ => ∂ (uncurryN n λ x₁' .. xₙ' => f y₁[xᵢ:=xᵢ'] .. yₘ[xᵢ:=xᵢ']) (x₁, .., xₙ) (dx₁, .., dxₙ)
```
 -/
def mkNormalTheoremLhsDifferential (e : Expr) (xs : Array Expr) : MetaM Expr := do

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
def mkNormalTheoremLhsTangentMap (e : Expr) (xs : Array Expr) : MetaM Expr := do

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
def mkNormalTheoremLhsAdjoint (e : Expr) (xs : Array Expr) : MetaM Expr := do
  
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
def mkNormalTheoremLhsAdjDiff (e : Expr) (xs : Array Expr) : MetaM Expr := do
  
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
def mkNormalTheoremLhsRevDiff (e : Expr) (xs : Array Expr) : MetaM Expr := do
  
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
def mkNormalTheoremLhs (transName : Name) (e : Expr) (xs : Array Expr) : MetaM Expr := do
  if transName == ``differential then
    mkNormalTheoremLhsDifferential e xs
  else if transName == ``tangentMap then
    mkNormalTheoremLhsTangentMap e xs
  else if transName == ``adjoint then
    mkNormalTheoremLhsAdjoint e xs
  else if transName == ``adjointDifferential then
    mkNormalTheoremLhsAdjDiff e xs
  else if transName == ``reverseDifferential then
    mkNormalTheoremLhsRevDiff e xs
  else
    throwError "Error in `mkNormalTheoremLhs`, unrecognized function transformation `{transName}`."


def mkNormalTheoremRhsType (transName : Name) (e : Expr) (xs : Array Expr) : MetaM Expr :=
  mkNormalTheoremLhs transName e xs >>= inferType


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

  let lhs ← mkNormalTheoremLhs transName e xs 

  let contextVars := maybeFilterContextVars transName xs contextVars

  lambdaTelescope lhs λ xs lhs => do

    let statement ← mkEq lhs (← mkAppM' defVal xs).headBeta

    mkForallFVars (contextVars.append xs) statement  >>= instantiateMVars
