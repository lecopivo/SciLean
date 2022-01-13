import SciLean.Algebra.Hilbert

namespace SciLean

class Basis (X : Type u) (ι : Type v) (K : Type w) where
  basis : ι → X
  proj  : ι → X → K

namespace Basis

  class Trait (X : Type u) where
    Index : Type v
    Coeff : Type w

  attribute [reducible] Trait.Index Trait.Coeff

  @[reducible] instance (X : Type u) (ι : Type v) (K : Type w) [Basis X ι K] : Trait X := ⟨ι, K⟩

  instance : Basis ℝ Unit ℝ := 
  {
    basis := λ _ => 1
    proj  := λ _ x => x
  }

  abbrev basis' {X} [Trait X] [Basis X (Trait.Index X) (Trait.Coeff X)]
    (i : (Trait.Index X)) : X := Basis.basis (Trait.Coeff X) i

  macro:max "𝔼" i:term : term => `(Basis.basis' $i)

  instance {X Y ι κ K} [Basis X ι K] [Basis Y κ K] [Zero X] [Zero Y] : Basis (X × Y) (ι ⊕ κ) K := 
  {
    basis := λ i =>
      match i with
      | Sum.inl ix => (basis' ix, 0)
      | Sum.inr iy => (0, basis' iy)
    proj := λ i x =>
      match i with
      | Sum.inl ix => proj ix x.1
      | Sum.inr iy => proj iy x.2
  }

end Basis

-- Finite dimensional vector space with explicit orthonormal basis
-- orthornormality shoud be enought to prove completeness of the basis etc.
-- The question is: Do we really want orthonormal basis be the norm? 
--     I'm not so sure about it. Definitely bad idea in math.
--     However, when programming objects are usually stored in containers
--     and these containers are indexed, so there is natural basis.
--     Why no to pick the orthonormal inner product on this basis?
-- open Basis Trait in
-- class FinVec (X : Type u) (ι : Type v) [Basis X ι ℝ] [Enumtype ι]  extends SemiHilbert X ℝ Unit (λ r _ => r) where
--   is_orthonormal : ∀ i j, ⟪(𝔼 i : X), (𝔼 j : X)⟫ = if i == j then (1 : ℝ) else (0 : ℝ)
--   inner_proj : ∀ i x, ⟪(𝔼 i : X), x⟫ = Basis.proj i x
  
-- namespace FinVec

--   instance : FinVec ℝ Unit :=
--   {
--     is_orthonormal := 
--     by
--       intro i j
--       simp [Basis.basis, Basis.basis', SemiInner.semiInner]
--       induction i; induction j; simp; done
--     inner_proj := 
--     by
--       intro i x
--       simp [Basis.basis, Basis.basis', Basis.proj, SemiInner.semiInner]
--       done
--   }

-- end FinVec
