import SciLean.Core
import SciLean.Data.DataArray
import SciLean.Data.ArrayType

namespace SciLean.ML

variable 
  {R : Type} [RealScalar R] [PlainDataType R]

set_default_scalar K

def dense {ι} [Index ι] (numOutputs : USize) 
  (weights : R^[numOutputs,ι]) (bias : R^[numOutputs]) (x : R^[ι]) : R^[numOutputs] := 
  ⊞ j => ∑ i, weights[(j,i)] * x[i] + bias[j]

#generate_revDeriv dense weights bias x
  prop_by unfold dense; fprop
  trans_by unfold dense; ftrans
