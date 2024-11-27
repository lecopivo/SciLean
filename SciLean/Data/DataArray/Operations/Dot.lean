import SciLean.Data.DataArray.Operations.Diag

namespace SciLean

open DataArrayN

def_fun_prop dot in x    with_transitive : IsContinuousLinearMap R
def_fun_prop dot in y    with_transitive : IsContinuousLinearMap R
def_fun_prop dot in x y  with_transitive : Differentiable R

#generate_linear_map_simps DataArrayN.dot.arg_x.IsLinearMap_rule
#generate_linear_map_simps DataArrayN.dot.arg_y.IsLinearMap_rule


abbrev_fun_trans dot in x y : fderiv R by
  rw[fderiv_wrt_prod (by fun_prop)]
  fun_trans

abbrev_fun_trans dot in x y : fwdFDeriv R by
  rw[fwdFDeriv_wrt_prod (by fun_prop)]
  autodiff

abbrev_fun_trans dot in x : adjoint R by
  equals (fun z => z•y) =>
    funext x
    apply AdjointSpace.ext_inner_left R
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[DataArrayN.inner_def, DataArrayN.dot,
         sum_over_prod, Function.HasUncurry.uncurry, sum_pull]
    ac_rfl

abbrev_fun_trans dot in y : adjoint R by
  equals (fun z => z•x) =>
    funext y
    apply AdjointSpace.ext_inner_left R
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[DataArrayN.inner_def, DataArrayN.dot,
         sum_over_prod, Function.HasUncurry.uncurry, sum_pull]
    ac_rfl

abbrev_fun_trans dot in x y : revFDeriv R by
  rw[revFDeriv_wrt_prod (by fun_prop)]
  unfold revFDeriv
  autodiff
