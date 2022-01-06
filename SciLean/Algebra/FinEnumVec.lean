import SciLean.Algebra.Hilbert

namespace SciLean

-- Finite explicit basis -- maybe over a ring? And then have `proj : index → X → K`
class FinEnumBasis (X : Type u) where
  index : Type 
  enumtype : Enumtype index
  basis : index → X
  proj  : index → X → ℝ  -- fast projection onto basis vectors

attribute [instance]  FinEnumBasis.enumtype

-- -- not sure about these
-- -- attribute [reducible] FinEnumBasis.ι FinEnumBasis.enumtype

def dimOf (X : Type u) [inst : FinEnumBasis X] := Enumtype.numOf inst.index

-- Notation for basis, the second case is when you need to specify the vector space X
macro:max "𝔼" i:term : term => `(FinEnumBasis.basis $i)

namespace FinEnumBasis

  instance : FinEnumBasis ℝ := 
  {
    index := Unit
    enumtype := by infer_instance
    basis := λ _ => 1
    proj  := λ _ x => x
  }

  instance {X Y} [FinEnumBasis X] [FinEnumBasis Y] [Zero X] [Zero Y] : FinEnumBasis (X × Y) := 
  {
    index := index X ⊕ index Y
    enumtype := by infer_instance
    basis := λ i =>
               match i with
                 | Sum.inl ix => (𝔼 ix, 0)
                 | Sum.inr iy => (0, 𝔼 iy)
    proj := λ i x =>
      match i with
      | Sum.inl ix => proj ix x.1
      | Sum.inr iy => proj iy x.2
  }

end FinEnumBasis

-- Finite dimensional vector space with explicit orthonormal basis
-- orthornormality shoud be enought to prove completeness of the basis etc.
-- The question is: Do we really want orthonormal basis be the norm? 
--     I'm not so sure about it. Definitely bad idea in math.
--     However, when programming objects are usually stored in containers
--     and these containers are indexed, so there is natural basis.
--     Why no to pick the orthonormal inner product on this basis?
class FinEnumVec (X : Type u) extends SemiHilbert X ℝ Unit (λ r _ => r), FinEnumBasis X where
  is_orthonormal : ∀ i j, ⟪(𝔼 i : X), (𝔼 j : X)⟫ = if i == j then (1 : ℝ) else (0 : ℝ)
  inner_proj : ∀ i x, ⟪(𝔼 i : X), x⟫ = FinEnumBasis.proj i x
  
namespace FinEnumVec

  instance : FinEnumVec ℝ :=
  {
    is_orthonormal := 
    by
      intro i j
      simp [FinEnumBasis.basis, SemiInner.semiInner]
      induction i; induction j; simp; done
    inner_proj := 
    by
      intro i x
      simp [FinEnumBasis.basis, FinEnumBasis.proj, SemiInner.semiInner]
      done
  }


end FinEnumVec
