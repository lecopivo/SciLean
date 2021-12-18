import SciLean.Algebra.Hilbert

namespace SciLean

-- Finite explicit basis
class FinEnumBasis (X : Type u) where
  index : Type 
  enumtype : Enumtype index
  basis : index → X

attribute [instance]  FinEnumBasis.enumtype

-- -- not sure about these
-- -- attribute [reducible] FinEnumBasis.ι FinEnumBasis.enumtype

def dimOf (X : Type u) [inst : FinEnumBasis X] := Enumtype.numOf inst.index

-- Notation for basis, the second case is when you need to specify the vector space X
macro:max "𝔼" i:term : term => `(FinEnumBasis.basis $i)

-- -- Finite dimensional vector space with explicit orthonormal basis
-- -- orthornormality shoud be enought to prove completeness of the basis etc.
-- -- The question is: Do we really want orthonormal basis be the norm? 
-- --     I'm not so sure about it. Definitely bad idea in math.
-- --     However, when programming objects are usually stored in containers
-- --     and these containers are indexed, so there is natural basis.
-- --     Why no to pick the orthonormal inner product on this basis?
class FinEnumVec (X : Type u) extends SemiHilbert' X SemiInner.RealSig, FinEnumBasis X where
  is_orthonormal : ∀ i j, ⟪(𝔼 i : X), (𝔼 j : X)⟫ = if i == j then 1 else 0
  
