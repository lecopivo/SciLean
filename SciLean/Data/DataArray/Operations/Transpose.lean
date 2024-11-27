import SciLean.Data.DataArray.Operations.Diag

namespace SciLean

variable
  {I : Type*} [IndexType I] [DecidableEq I]
  {J : Type*} [IndexType J] [DecidableEq J]
  {R : Type*} [RealScalar R] [PlainDataType R]


open DataArrayN

def_fun_prop transpose in A
  with_transitive
  [RealScalar R] : IsContinuousLinearMap R

#generate_linear_map_simps DataArrayN.transpose.arg_A.IsLinearMap_rule


-- todo: change to abbrev_def_trans
def_fun_trans transpose in A [RealScalar R] : fderiv R by autodiff

-- todo: change to abbrev_def_trans
def_fun_trans transpose in A [RealScalar R] : fwdFDeriv R by autodiff

-- todo: change to abbrev_def_trans
def_fun_trans transpose in A [RealScalar R] : adjoint R by
  equals (fun B => B.transpose) =>
    funext x
    apply AdjointSpace.ext_inner_left R
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[DataArrayN.inner_def,Function.HasUncurry.uncurry,
         DataArrayN.transpose,sum_over_prod]
    rw[sum_swap]

-- todo: change to abbrev_def_trans
def_fun_trans transpose in A [RealScalar R] : revFDeriv R by unfold revFDeriv; autodiff
