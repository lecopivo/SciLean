import SciLean.Core.Hilbert

namespace SciLean

class Basis (X : Type u) (ι : outParam $ Type v) (K : outParam $ Type w) where
  basis : ι → X
  proj  : ι → X → K


namespace Basis

  instance : Basis ℝ Unit ℝ := 
  {
    basis := λ _ => 1
    proj  := λ _ x => x
  }

  macro:max "𝕖" i:term : term => `(Basis.basis $i)

  instance {X Y ι κ K} [Basis X ι K] [Basis Y κ K] [Zero X] [Zero Y] : Basis (X × Y) (ι ⊕ κ) K := 
  {
    basis := λ i =>
      match i with
      | Sum.inl ix => (Basis.basis ix, 0)
      | Sum.inr iy => (0, Basis.basis iy)
    proj := λ i x =>
      match i with
      | Sum.inl ix => proj ix x.1
      | Sum.inr iy => proj iy x.2
  }

end Basis

/--
 -/
class FinVec (X : Type) (ι : outParam Type) [outParam $ Enumtype ι] extends Hilbert X, Basis X ι ℝ where
  is_basis : ∀ x : X, x = ∑ i : ι, Basis.proj i x * Basis.basis (X:=X) i
  -- TODO: add some condition that the basis vectors are linearly independent




instance : Basis ℝ Unit ℝ where
  basis _ := 1
  proj _ x := x

instance : FinVec ℝ Unit where
  is_basis := sorry_proof
  

opaque foo {X} {ι : Type} [Enumtype ι] [FinVec X ι] (x : X) : X

set_option pp.all true in
#check foo (1 : ℝ)
