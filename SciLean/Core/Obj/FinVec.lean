import SciLean.Algebra

namespace SciLean

  class Basis (X : Type u) (ι : outParam $ Type v) (K : outParam $ Type w) where
    basis : ι → X
    proj  : ι → X → K

  macro:max "𝔼" i:term : term => `(Basis.basis $i)

  class FinVec (X : Type) (ι : Type) [outParam $ Enumtype ι] extends Hilbert X, Basis X ι ℝ

  instance : Basis ℝ Unit ℝ :=
  {
    basis := λ _ => 1
    proj  := λ _ x => x
  }

  instance : FinVec ℝ Unit := FinVec.mk
