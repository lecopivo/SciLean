import SciLean.Data.DataArray.Operations.Diag

namespace SciLean

open DataArrayN

def_fun_prop vecmul in A    with_transitive : IsContinuousLinearMap R
def_fun_prop vecmul in x    with_transitive : IsContinuousLinearMap R
def_fun_prop vecmul in A x  with_transitive : Differentiable R

#generate_linear_map_simps DataArrayN.vecmul.arg_A.IsLinearMap_rule
#generate_linear_map_simps DataArrayN.vecmul.arg_x.IsLinearMap_rule


-- todo: change to abbrev_def_trans
def_fun_trans vecmul in A x : fderiv R by
  rw[fderiv_wrt_prod (by fun_prop)]
  fun_trans

-- todo: change to abbrev_def_trans
def_fun_trans vecmul in A x : fwdFDeriv R by
  rw[fwdFDeriv_wrt_prod (by fun_prop)]
  autodiff

-- todo: change to abbrev_def_trans
def_fun_trans vecmul in A : adjoint R by
  equals (fun y => y.outerprod x) =>
    funext y
    apply AdjointSpace.ext_inner_left R
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[DataArrayN.inner_def, DataArrayN.vecmul, DataArrayN.outerprod,
         sum_over_prod, Function.HasUncurry.uncurry, sum_pull]
    ac_rfl

-- todo: change to abbrev_def_trans
def_fun_trans vecmul in x : adjoint R by
  equals (fun y => A.transpose.vecmul y) =>
    funext y
    apply AdjointSpace.ext_inner_left R
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[DataArrayN.inner_def, DataArrayN.vecmul, DataArrayN.transpose,
         sum_over_prod, Function.HasUncurry.uncurry, sum_pull]
    rw[sum_swap]
    ac_rfl

-- todo: change to abbrev_def_trans
def_fun_trans vecmul in A x : revFDeriv R by
  rw[revFDeriv_wrt_prod (by fun_prop)]
  unfold revFDeriv
  autodiff
