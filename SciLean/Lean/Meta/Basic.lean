import Lean
import Std.Lean.Expr

import SciLean.Lean.Array

namespace Lean.Meta

def getConstExplicitArgIdx (constName : Name) : MetaM (Array Nat) := do
  let info ← getConstInfo constName
  
  let (_, explicitArgIdx) ← forallTelescope info.type λ Xs _ => do
    Xs.foldlM (init := (0,(#[] : Array Nat))) 
      λ (i, ids) X => do 
        if (← X.fvarId!.getBinderInfo).isExplicit then
          pure (i+1, ids.push i)
        else
          pure (i+1, ids)

  return explicitArgIdx

def getConstArity (constName : Name) : MetaM Nat := do
  let info ← getConstInfo constName
  return info.type.forallArity


/--
  Same as `mkAppM` but does not leave trailing implicit arguments.

  For example for `foo : (X : Type) → [OfNat 0 X] → X` the ``mkAppNoTrailingM `foo #[X]`` produces `foo X : X` instead of `@foo X : [OfNat 0 X] → X`
-/
def mkAppNoTrailingM (constName : Name) (xs : Array Expr) : MetaM Expr := do

  let n ← getConstArity constName
  let explicitArgIds ← getConstExplicitArgIdx constName

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
