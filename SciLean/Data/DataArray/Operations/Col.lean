import SciLean.Data.DataArray.Operations.Curry
import SciLean.Data.ArrayOperations.Operations.GetElem


namespace SciLean.DataArrayN


data_array_fun_prop col X R in x : IsLinearMap R by sorry_proof
data_array_fun_prop col X R in x : Continuous by sorry_proof
data_array_fun_prop col X R in x : IsContinuousLinearMap R by constructor <;> fun_prop
data_array_fun_prop col X R in x : Differentiable R by fun_prop


data_array_data_synth_abbrev DataArrayN.col X R in x (x₀) : (HasFDerivAt (𝕜:=R) · · x₀) by
  apply hasFDerivAt_from_isContinuousLinearMap
  fun_prop

data_array_data_synth_abbrev DataArrayN.col X R in x : HasFwdFDeriv R by
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth
  case simp => intros; simp; rfl
