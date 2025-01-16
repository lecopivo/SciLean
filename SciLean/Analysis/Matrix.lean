import Mathlib.Analysis.Matrix

import SciLean.Analysis.AdjointSpace.Adjoint

namespace SciLean

-- We make `Matrix m n α` normed space globally
attribute [instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable
    {R m n α : Type*}
    [IndexType m] [IndexType n]

instance [AddCommMonoid R] [Inner R α] : Inner R (Matrix m n α) := by
  unfold Matrix
  infer_instance

instance [RCLike R] [NormedAddCommGroup α] [AdjointSpace R α] : AdjointSpace R (Matrix m n α) where
  inner_top_equiv_norm := sorry_proof
  conj_symm := sorry_proof
  add_left := sorry_proof
  smul_left := sorry_proof
