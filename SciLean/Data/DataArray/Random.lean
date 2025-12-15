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
def rand (r : SciLean.Rand X) : SciLean.Rand (X^[I]) :=
  { spec := default
    rand := fun g => Id.run do
      let mut data : DataArray X := DataArray.mkZero nI
      let mut g := g
      for j in [0:nI] do
        let (x, g') := r.rand g
        g := g'
        let i : Idx data.size := ⟨j.toUSize, sorry_proof⟩
        data := data.set i x
      return (⟨data, sorry_proof⟩, g) }

end SciLean.DataArrayN
