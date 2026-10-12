module

public import SciLean.Core
public import SciLean.Data.DataArray
public import SciLean.Data.ArrayType
public import SciLean.Data.Prod
public import SciLean.Core.Functions.Exp

@[expose] public section


namespace SciLean.ML

open Scalar in
def crossEntropy {ι} [Index ι] [RealScalar R] [PlainDataType R]
  (ε : R) (actual predicted : R^ι) : R :=
  let w : R := -1/(Index.size ι).toNat
  w • ∑ i, actual[i] * log (ε + predicted[i])

#generate_revDeriv crossEntropy predicted
  prop_by unfold crossEntropy; fprop
  trans_by unfold crossEntropy; ftrans
