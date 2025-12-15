import SciLean.Data.DataArray.DataArray
import SciLean.Data.DataArray.Operations

import SciLean.Probability.Rand

namespace SciLean.DataArrayN

variable {X : Type} [PlainDataType X]
variable {I : Type*} {nI : Nat} [IndexType I nI]

/-- Generate a random array by sampling `nI` times from `r`.

This iterates over the linear index type `Idx nI` so it does not require any
`FoldM I` instance for the index type `I`.
-/
@[inline]
def rand (r : SciLean.Rand X) : SciLean.Rand (X^[I]) := do
  let mut data : DataArray X := DataArray.mkZero nI
  for i in fullRange (Idx nI) do
    data := data.set ⟨i.1, sorry_proof⟩ (← r)
  return ⟨data, sorry_proof⟩

end SciLean.DataArrayN
