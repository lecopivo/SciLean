import SciLean
import SciLean.Core.Meta.GenerateRevCDeriv'

namespace SciLean.ML

variable 
  {K : Type} [RealScalar K]
  {W : Type} [Vec K W]

set_default_scalar K

variable {α β κ ι : Type} [Index κ] [Index ι] [PlainDataType K] [PlainDataType R]

variable (κ)
def dense (weights : K^(κ×ι)) (bias : K^κ) (x : K^ι) : K^κ := 
  ⊞ j => ∑ i, weights[(j,i)] * x[i] + bias[j]
variable {κ}

#generate_revDeriv dense weights bias x
  prop_by unfold dense; fprop
  trans_by unfold dense; ftrans
