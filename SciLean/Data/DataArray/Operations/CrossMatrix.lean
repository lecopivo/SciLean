import SciLean.Data.DataArray.Operations.Multiply

namespace SciLean

open DataArrayN

def_fun_prop crossmatrix in x
  with_transitive : IsContinuousLinearMap R by sorry_proof

#generate_linear_map_simps DataArrayN.crossmatrix.arg_x.IsLinearMap_rule

abbrev_fun_trans crossmatrix in x : fderiv R by autodiff

abbrev_fun_trans crossmatrix in x : fwdFDeriv R by autodiff

abbrev_fun_trans crossmatrix in x : adjoint R by
  equals (fun A => A.antisymmpart) =>
    sorry_proof

abbrev_fun_trans crossmatrix in x : revFDeriv R by
  unfold revFDeriv
  autodiff

abbrev_fun_trans crossmatrix in x : revFDerivProj R Unit by
  unfold revFDerivProj
  autodiff

abbrev_fun_trans crossmatrix in x : revFDerivProjUpdate R Unit by
  unfold revFDerivProjUpdate
  autodiff
