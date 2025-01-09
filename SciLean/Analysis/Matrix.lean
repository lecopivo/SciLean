import Mathlib.Analysis.Matrix

import SciLean.Analysis.AdjointSpace.Adjoint

namespace SciLean

-- We make `Matrix m n α` normed space globally
attribute [instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable
    {R m n α : Type*}
    [Fintype m] [Fintype n]

instance [AddCommMonoid R] [Inner R α] : Inner R (Matrix m n α) := ⟨fun A B =>
  Finset.univ.sum fun i => Finset.univ.sum fun j => Inner.inner (A i j) (B i j)⟩

instance [RCLike R] [NormedAddCommGroup α] [AdjointSpace R α] : AdjointSpace R (Matrix m n α) where
  inner_top_equiv_norm := sorry_proof
  conj_symm := sorry_proof
  add_left := sorry_proof
  smul_left := sorry_proof
