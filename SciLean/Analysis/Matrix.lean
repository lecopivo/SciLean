import Mathlib.Analysis.Matrix

import SciLean.Analysis.AdjointSpace.Adjoint

namespace SciLean

-- We make `Matrix m n α` normed space globally
attribute [instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable
    {R I J α : Type*} {nI nJ : ℕ}
    [IndexType I nI] [IndexType J nJ] [Fold I] [Fold J]

instance [AddCommMonoid R] [Inner R α] : Inner R (Matrix I J α) :=
  show Inner R (I → J → α) from inferInstance

instance [RCLike R] [NormedAddCommGroup α] [AdjointSpace R α] : AdjointSpace R (Matrix I J α) where
  inner_top_equiv_norm := sorry_proof
  conj_symm := sorry_proof
  add_left := sorry_proof
  smul_left := sorry_proof
