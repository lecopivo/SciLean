import SciLean.Data.DataArray.Operations.Diag

namespace SciLean


open DataArrayN

def_fun_prop antisymmpart in A
  with_transitive
  [RealScalar R] : IsContinuousLinearMap R by sorry_proof

#generate_linear_map_simps DataArrayN.antisymmpart.arg_A.IsLinearMap_rule

abbrev_fun_trans antisymmpart in A : fderiv R by
  fun_trans

abbrev_fun_trans antisymmpart in A : fwdFDeriv R by
  autodiff

abbrev_fun_trans antisymmpart in A : adjoint R by
  equals (fun x => x.crossmatrix) =>
    sorry_proof

abbrev_fun_trans antisymmpart in A : revFDeriv R by
  unfold revFDeriv
  autodiff

abbrev_fun_trans antisymmpart in A : revFDerivProj R Unit by
  unfold revFDerivProj
  autodiff

abbrev_fun_trans antisymmpart in A : revFDerivProjUpdate R Unit by
  unfold revFDerivProjUpdate
  autodiff
