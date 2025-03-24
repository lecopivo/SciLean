import Mathlib.Algebra.Module.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import SciLean.Analysis.Scalar
import SciLean.Util.RewriteBy

namespace SciLean


/-- Dimension of `X` over the ring `R` is `dim`.

The need for this typeclass comes when we want to write code, the function `Module.finrank` is
noncomputable. This calss allow you to add implicit argument `dim` which will be resolved   -/
class Dimension (R : Type*) (X : Type*) (dim : outParam ℕ) [Ring R] [AddCommGroup X] [Module R X] where
  is_dim : Module.finrank R X = dim


open Lean Meta Elab Qq in
/-- Dimension of `X`.

The dimension is over the default scalar `R` set with
```
set_default_scalar R
``` -/
elab "dim(" X:term ")" : term => do

  let R ← Term.elabTerm (← `(defaultScalar%)) none
  let X ← Term.elabTerm X none

  -- I have no idea what is the idiomatic way to synthesize instance with out parameters
  let Dim ← mkAppOptM ``Dimension #[R,X]
  let (xs,_,_) ← forallMetaTelescope (← inferType Dim)
  xs[1]!.mvarId!.synthInstance
  xs[2]!.mvarId!.synthInstance
  xs[3]!.mvarId!.synthInstance
  let _ ← synthInstance (mkAppN Dim xs)

  let dim ← instantiateMVars xs[0]!
  let (dim,_) ← elabConvRewrite dim #[] (← `(conv| simp -failIfUnchanged))
  return dim

@[simp, simp_core]
theorem finrank_dimension {R X d} [Ring R] [AddCommGroup X] [Module R X] [hd : Dimension R X d] :
  Module.finrank R X = d := hd.is_dim



instance : Dimension ℝ ℝ 1 where
  is_dim := by simp

instance : Dimension ℝ ℂ 2 where
  is_dim := sorry_proof

instance : Dimension ℂ ℂ 1 where
  is_dim := sorry_proof

instance [Scalar R C] : Dimension C C 1 where
  is_dim := by simp

instance [RealScalar R] : Dimension ℝ R 1 where
  is_dim := sorry_proof

instance {R} [Field R] {n m}
    {X} [AddCommGroup X] [Module R X] [Module.Finite R X] [dX : Dimension R X n]
    {Y} [AddCommGroup Y] [Module R Y] [Module.Finite R Y] [dY : Dimension R Y m] :
    Dimension R (X×Y) (n+m) where
  is_dim := by
    simp [dX.is_dim, dY.is_dim]

-- instance {R} [Field R] {n}
--     {I} [IndexType I]
--     {X} [AddCommGroup X] [Module R X] [Module.Finite R X] [_dX : Dimension R X n] :
--     Dimension R (I → X) (size I * n) where
--   is_dim := by sorry_proof
