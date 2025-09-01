import SciLean.Data.DataArray.Operations.Curry
import SciLean.Data.ArrayOperations.Operations.GetElem


namespace SciLean.DataArrayN


data_array_fun_prop row X R in x : IsLinearMap R by sorry_proof
data_array_fun_prop row X R in x : Continuous by sorry_proof
data_array_fun_prop row X R in x : IsContinuousLinearMap R by constructor <;> fun_prop
data_array_fun_prop row X R in x : Differentiable R by fun_prop


data_array_data_synth_abbrev DataArrayN.row X R in x (x₀) : (HasFDerivAt (𝕜:=R) · · x₀) by
  apply hasFDerivAt_from_isContinuousLinearMap
  fun_prop

data_array_data_synth_abbrev DataArrayN.row X R in x : HasFwdFDeriv R by
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth
  case simp => intros; simp; rfl

data_array_data_synth_abbrev DataArrayN.row X R in x : HasAdjoint R by
  unfold row
  data_synth => skip

data_array_data_synth_abbrev DataArrayN.row X R in x : HasAdjointUpdate R by
  conv => enter[3]; assign (fun (x : X^[J]) (A : X^[I,J]) =>
                             let A := A.curry
                             let ai := A[i]
                             let A := (setElem A i (ai + x) .intro).uncurry
                             A)
  apply hasAdjointUpdate_from_hasAdjoint
  case adjoint => data_synth
  case simp => intros; simp; ext ⟨i,j⟩; sorry_proof --simp[uncurry_getElem]; sorry_proof

data_array_data_synth_abbrev DataArrayN.row X R in x : HasRevFDeriv R by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl

data_array_data_synth_abbrev DataArrayN.row X R in x : HasRevFDerivUpdate R by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl
