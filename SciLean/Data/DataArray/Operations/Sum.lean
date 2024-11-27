import SciLean.Data.DataArray.Operations.Diag

namespace SciLean

variable
  {I : Type*} [IndexType I] [DecidableEq I]
  {J : Type*} [IndexType J] [DecidableEq J]
  {R : Type*} [RealScalar R] [PlainDataType R]

open DataArrayN

def_fun_prop sum in x with_transitive : IsContinuousLinearMap R

#generate_linear_map_simps DataArrayN.sum.arg_x.IsLinearMap_rule

abbrev_fun_trans sum in x : fderiv R by fun_trans

abbrev_fun_trans sum in x : fwdFDeriv R by autodiff

abbrev_fun_trans sum in x : adjoint R by
  equals (fun x' => x' • 1) =>
    funext x
    apply AdjointSpace.ext_inner_left R
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[DataArrayN.inner_def,Function.HasUncurry.uncurry,
         DataArrayN.sum, sum_pull]

abbrev_fun_trans sum in x : revFDeriv R by
  unfold revFDeriv
  autodiff
