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




----------------------------------------------------------------------------------------------------

#check zero_mul
#check mul_zero
namespace DataArrayN

variable
  {I : Type*} [IndexType I] [DecidableEq I]
  {J : Type*} [IndexType J] [DecidableEq J]
  {K : Type*} [IndexType K] [DecidableEq K]
  {R : Type*} [RealScalar R] [PlainDataType R]

@[simp, simp_core]
theorem identity_vecmul (x : R^[I]) : Matrix.identity (R:=R) (I:=I) * x = A := sorry

@[simp, simp_core]
theorem zero_vecmul (b : R^[J]) : (0 : R^[I,J]) * b = 0 := sorry

@[simp, simp_core]
theorem vecmul_zero (A : R^[I,J]) : A * (0 : R^[J]) = 0 := sorry

end DataArrayN


variable
  {I : Type*} [IndexType I] [DecidableEq I]
  {J : Type*} [IndexType J] [DecidableEq J]
  {K : Type*} [IndexType K] [DecidableEq K]
  {R : Type*} [RealScalar R] [PlainDataType R]


def_fun_prop _matrixvec (b : R^[J]) : IsContinuousLinearMap R (fun A : R^[I,J] => A * b) by
  simp[HMul.hMul]; fun_prop

def_fun_prop _matrixvec (A : R^[I,J]) : IsContinuousLinearMap R (fun b : R^[J] => A * b) by
  simp[HMul.hMul]; fun_prop

def_fun_prop _matrixvec : Differentiable R (fun Ab : R^[I,J] × R^[J] => Ab.1 * Ab.2) by
  simp[HMul.hMul]; fun_prop

abbrev_fun_trans _matrixvec : fderiv R (fun Ab : R^[I,J] × R^[J] => Ab.1 * Ab.2) by
  rw[fderiv_wrt_prod]
  fun_trans

abbrev_fun_trans _matrixvec : fwdFDeriv R (fun Ab : R^[I,J] × R^[J] => Ab.1 * Ab.2) by
  rw[fwdFDeriv_wrt_prod]; unfold fwdFDeriv; autodiff

abbrev_fun_trans _matrixvec (b : R^[J]) : adjoint R (fun A : R^[I,J] => A * b) by
  equals (fun c => c.outerprod b) =>
    simp[HMul.hMul]; fun_trans; rfl

abbrev_fun_trans _matrixvec (A : R^[I,J]) : adjoint R (fun b : R^[J] => A * b) by
  equals (fun c => Aᵀ * c) =>
    simp[HMul.hMul]; fun_trans; rfl

abbrev_fun_trans _matrixvec : revFDeriv R (fun Ab : R^[I,J] × R^[J] => Ab.1 * Ab.2) by
  rw[revFDeriv_wrt_prod]; unfold revFDeriv; autodiff
