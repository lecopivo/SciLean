import SciLean.Data.Idx.Basic
import SciLean.Data.IndexType.Basic
import SciLean.Data.ArrayOperations.Basic


namespace SciLean

/-- Get element of `X` by indexing with `Idx n` -/
class GetElemIdx (X : Type*) (n : Nat) (Y : outParam Type*) where
  getElemIdx (x : X) (i : Idx n) : Y

export GetElemIdx (getElemIdx)

class LawfulGetElemIdx (X : Type*) (I : Type*) {Y : outParam Type*} {n : outParam Nat} [IndexType I n]
      [GetElem' X I Y] [GetElemIdx X n Y] where

  getElem_eq_getElemIdx (x : X) (i : I) : getElem x i .intro = getElemIdx x (toIdx i)
