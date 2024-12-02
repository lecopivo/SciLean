import SciLean.Data.DataArray.Operations.Multiply

namespace SciLean


variable
  {I : Type*} [IndexType I] [DecidableEq I]
  {R : Type*} [RealScalar R] [PlainDataType R]


open DataArrayN

def_fun_prop diag in x
  with_transitive : IsContinuousLinearMap R

#generate_linear_map_simps DataArrayN.diag.arg_x.IsLinearMap_rule

abbrev_fun_trans diag in x : fderiv R by autodiff

abbrev_fun_trans diag in x : fwdFDeriv R by autodiff

abbrev_fun_trans diag in x : adjoint R by
  equals (fun x' => x'.diagonal) =>
    funext x
    apply AdjointSpace.ext_inner_left R
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[DataArrayN.inner_def,Function.HasUncurry.uncurry,
         DataArrayN.diag,DataArrayN.diagonal,
         sum_over_prod, sum_ite']

abbrev_fun_trans diag in x : revFDeriv R by
  unfold revFDeriv
  autodiff

abbrev_fun_trans diag in x : revFDerivProj R Unit by
  unfold revFDerivProj
  autodiff

abbrev_fun_trans diag in x : revFDerivProjUpdate R Unit by
  unfold revFDerivProjUpdate
  autodiff
