import SciLean.Data.DataArray.Operations.Multiply

namespace SciLean

open DataArrayN

def_fun_prop lowerTriangular in x
  with_transitive : IsContinuousLinearMap R

#generate_linear_map_simps DataArrayN.lowerTriangular.arg_x.IsLinearMap_rule

abbrev_fun_trans lowerTriangular in x : fderiv R by autodiff

abbrev_fun_trans lowerTriangular in x : fwdFDeriv R by autodiff

abbrev_fun_trans lowerTriangular in x : adjoint R by
  equals (fun A => lowerTriangularPart A offset (by assumption)) =>
    sorry_proof

abbrev_fun_trans lowerTriangular in x : revFDeriv R by
  unfold revFDeriv
  autodiff

abbrev_fun_trans lowerTriangular in x : revFDerivProj R Unit by
  unfold revFDerivProj
  autodiff

abbrev_fun_trans lowerTriangular in x : revFDerivProjUpdate R Unit by
  unfold revFDerivProjUpdate
  autodiff
