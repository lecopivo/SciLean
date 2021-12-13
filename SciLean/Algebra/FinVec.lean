import Mathlib.Init.Set

import SciLean.Mathlib.Data.Enumtype
import SciLean.Algebra.Hilbert

namespace SciLean

-- Basis is a subset of 
class Basis (X : Type) where
  basisSet : Set X

class FinEnumBasis (X : Type) extends Basis X where
  Index : Type
  indexEnum : Enumtype Index
  basisElem : Index → X
  valid : (∀ i, basisElem i ∈ Basis.basisSet) ∧
          (∀ e ∈ Basis.basisSet, ∃ i, e = basisElem i)

attribute [reducible] FinEnumBasis.Index    -- We probably want to usually see throuh it
attribute [instance] FinEnumBasis.indexEnum

-- example (X) [FinEnumBasis X] : Enumtype (FinEnumBasis.Index X) := by infer_instance

-- open FinEnumBasis (basisElem)
-- #check FinEnumBasis.basisElem
-- abbrev basisElem {X} [FinEnumBasis X] (i : FinEnumBasis.Index X) := FinEnumBasis.basisElem i

-- #check FinEnumBasis.basisElem

prefix:max "𝑬" => FinEnumBasis.basisElem

open FinEnumBasis in
class FinEnumVec (X : Type) extends Hilbert X, FinEnumBasis X where
  basis_compatiblity : ∀ (x y : X), ⟪x, y⟫ = ∑ i, ⟪x, 𝑬 i⟫*⟪y, 𝑬 i⟫
  orthonormality : ∀ (i j : Index), if i == j 
                            then ⟪𝑬 i, 𝑬 j⟫ = (1 : ℝ)
                            else ⟪𝑬 i, 𝑬 j⟫ = (0 : ℝ)
