import SciLean.Data.DataArray.Operations.Diag

namespace SciLean

variable
  {I : Type*} [IndexType I] [DecidableEq I]
  {J : Type*} [IndexType J] [DecidableEq J]
  {R : Type*} [RealScalar R] [PlainDataType R]


open DataArrayN

def_fun_prop outerprod in x    with_transitive : IsContinuousLinearMap R
def_fun_prop outerprod in y    with_transitive : IsContinuousLinearMap R
def_fun_prop outerprod in x y  with_transitive : Differentiable R

#generate_linear_map_simps DataArrayN.outerprod.arg_x.IsLinearMap_rule
#generate_linear_map_simps DataArrayN.outerprod.arg_y.IsLinearMap_rule


-- todo: change to abbrev_def_trans
def_fun_trans outerprod in x y : fderiv R by
  rw[fderiv_wrt_prod (by fun_prop)]
  fun_trans

-- todo: change to abbrev_def_trans
def_fun_trans outerprod in x y : fwdFDeriv R by
  rw[fwdFDeriv_wrt_prod (by fun_prop)]
  autodiff

-- todo: change to abbrev_def_trans
def_fun_trans outerprod in x : adjoint R by
  equals (fun A => A.vecmul y) =>
    funext x
    apply AdjointSpace.ext_inner_left R
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[DataArrayN.inner_def, DataArrayN.outerprod, DataArrayN.vecmul,
         sum_over_prod, Function.HasUncurry.uncurry, sum_pull]
    ac_rfl

-- todo: change to abbrev_def_trans
def_fun_trans outerprod in y : adjoint R by
  equals (fun A => A.transpose.vecmul x) =>
    funext y
    apply AdjointSpace.ext_inner_left R
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[DataArrayN.inner_def, DataArrayN.outerprod, DataArrayN.vecmul, DataArrayN.transpose,
         sum_over_prod, Function.HasUncurry.uncurry, sum_pull]
    rw[sum_swap]
    ac_rfl

-- todo: change to abbrev_def_trans
def_fun_trans outerprod in x y : revFDeriv R by
  rw[revFDeriv_wrt_prod (by fun_prop)]
  unfold revFDeriv
  autodiff
