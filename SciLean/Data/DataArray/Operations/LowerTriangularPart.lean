import SciLean.Data.DataArray.Operations.Multiply

namespace SciLean

open DataArrayN

def_fun_prop lowerTriangularPart in A
  with_transitive : IsContinuousLinearMap R by sorry_proof

#generate_linear_map_simps DataArrayN.lowerTriangularPart.arg_A.IsLinearMap_rule

abbrev_fun_trans lowerTriangularPart in A : fderiv R by autodiff

abbrev_fun_trans lowerTriangularPart in A : fwdFDeriv R by autodiff

abbrev_fun_trans lowerTriangularPart in A : adjoint R by
  equals (fun x => lowerTriangular x n offset h) =>
    sorry_proof

abbrev_fun_trans lowerTriangularPart in A : revFDeriv R by
  unfold revFDeriv
  autodiff
