import Mathlib
import SciLean.Data.IndexType.Basic

namespace SciLean

open IndexType


/--  -/
structure IndexInclusion (I J : Type*) [IndexType I] [IndexType J]
  extends I ≃ J
  where
  toFin_toFun :
    (h : 0 < size I) →
    ∀ i, (toFin (toFun i)).1 - (toFin (toFun (fromFin ⟨0,h⟩))).1 = (toFin i).1
