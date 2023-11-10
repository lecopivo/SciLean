import SciLean
import SciLean.Core.Meta.GenerateRevCDeriv'

namespace SciLean.ML

variable 
  {K : Type} [RealScalar K]
  {W : Type} [Vec K W]

set_default_scalar K

variable {α β κ ι : Type} [Index κ] [Index ι] [PlainDataType K] [PlainDataType R]

variable (κ)
def denseLazy (weights : κ → ι → K) (bias : κ → K) (x : ι → K) (j : κ) : K := 
  ∑ i, weights j i * x i + bias j
variable {κ}

#generate_revCDeriv' denseLazy weights bias x | j
  prop_by unfold denseLazy; fprop
  trans_by 
    unfold denseLazy
    autodiff

variable (κ)
def dense (weights : DataArrayN K (κ×ι)) (bias : K^κ) (x : K^ι) : K^κ := 
  -- ⊞ j => ∑ i, weights[(j,i)] * x[i] + bias[j]
  ⊞ j => denseLazy κ (fun j i => weights[(j,i)]) (fun j => bias[j]) (fun i => x[i]) j
variable {κ}

#generate_revCDeriv' dense weights bias x
  prop_by unfold dense; fprop
  trans_by unfold dense; autodiff
