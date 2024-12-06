import SciLean.Data.DataArray.Operations.Diag

namespace SciLean



variable
  {I : Type*} [IndexType I] [DecidableEq I]
  {R : Type*} [RealScalar R] [PlainDataType R]

open DataArrayN


def_fun_prop diagonal in x
  with_transitive
  [RealScalar R] : IsContinuousLinearMap R

#generate_linear_map_simps DataArrayN.diagonal.arg_x.IsLinearMap_rule

abbrev_fun_trans diagonal in x [RealScalar R] : fderiv R by
  fun_trans

abbrev_fun_trans diagonal in x [RealScalar R] : fwdFDeriv R by
  autodiff

abbrev_fun_trans diagonal in x [DecidableEq I] [RealScalar R] : adjoint R by
  equals (fun x' => x'.diag) =>
    funext x
    apply AdjointSpace.ext_inner_left R
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[DataArrayN.inner_def,Function.HasUncurry.uncurry,
         DataArrayN.diagonal,DataArrayN.diag,
         sum_prod_eq_sum_sum, sum_ite']

abbrev_fun_trans diagonal in x [DecidableEq I] [RealScalar R] : revFDeriv R by
  unfold revFDeriv
  autodiff
