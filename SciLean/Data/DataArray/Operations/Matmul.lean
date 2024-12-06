import SciLean.Data.DataArray.Operations.Diag

namespace SciLean

open DataArrayN

def_fun_prop matmul in A    with_transitive : IsContinuousLinearMap R
def_fun_prop matmul in B    with_transitive : IsContinuousLinearMap R
def_fun_prop matmul in A B  with_transitive : Differentiable R

#generate_linear_map_simps DataArrayN.matmul.arg_A.IsLinearMap_rule
#generate_linear_map_simps DataArrayN.matmul.arg_B.IsLinearMap_rule


abbrev_fun_trans matmul in A B : fderiv R by
  rw[fderiv_wrt_prod (by fun_prop)]
  fun_trans

abbrev_fun_trans matmul in A B : fwdFDeriv R by
  rw[fwdFDeriv_wrt_prod (by fun_prop)]
  autodiff

abbrev_fun_trans matmul in A : adjoint R by
  equals (fun C => C.matmul B.transpose) =>
    funext C
    apply AdjointSpace.ext_inner_left R
    intro D
    rw[← adjoint_ex _ (by fun_prop)]
    simp[DataArrayN.inner_def, DataArrayN.matmul, DataArrayN.transpose,
         sum_prod_eq_sum_sum, Function.HasUncurry.uncurry, sum_pull]
    conv => lhs; enter[1,i]; rw[sum_swap]
    ac_rfl

abbrev_fun_trans matmul in B : adjoint R by
  equals (fun C => A.transpose.matmul C) =>
    funext C
    apply AdjointSpace.ext_inner_left R
    intro D
    rw[← adjoint_ex _ (by fun_prop)]
    simp[DataArrayN.inner_def, DataArrayN.matmul, DataArrayN.transpose,
         sum_prod_eq_sum_sum, Function.HasUncurry.uncurry, sum_pull]
    conv => lhs; enter[1,i]; rw[sum_swap]
    rw[sum_swap]
    conv => lhs; enter[1,i]; rw[sum_swap]
    ac_rfl

abbrev_fun_trans matmul in A B : revFDeriv R by
  rw[revFDeriv_wrt_prod (by fun_prop)]
  unfold revFDeriv
  autodiff

abbrev_fun_trans matmul in A B : revFDerivProj R Unit by
  rw[revFDerivProj_wrt_prod (by fun_prop)]
  unfold revFDerivProj
  autodiff

abbrev_fun_trans matmul in A B : revFDerivProjUpdate R Unit by
  rw[revFDerivProjUpdate_wrt_prod (by fun_prop)]
  unfold revFDerivProjUpdate
  autodiff




----------------------------------------------------------------------------------------------------


variable
  {I : Type} [IndexType I] [DecidableEq I]
  {J : Type} [IndexType J] [DecidableEq J]
  {K : Type} [IndexType K] [DecidableEq K]
  {R : Type} [RealScalar R] [PlainDataType R]


def_fun_prop _matrix (B : R^[J,K]) : IsContinuousLinearMap R (fun A : R^[I,J] => A * B) by
  simp[HMul.hMul]; fun_prop

def_fun_prop _matrix (A : R^[I,J]) : IsContinuousLinearMap R (fun B : R^[J,K] => A * B) by
  simp[HMul.hMul]; fun_prop

def_fun_prop _matrix : Differentiable R (fun AB : R^[I,J] × R^[J,K] => AB.1 * AB.2) by
  simp[HMul.hMul]; fun_prop

abbrev_fun_trans _matrix : fderiv R (fun AB : R^[I,J] × R^[J,K] => AB.1 * AB.2) by
  rw[fderiv_wrt_prod]
  fun_trans

abbrev_fun_trans _matrix (B : R^[J,K]) : fwdFDeriv R (fun A : R^[I,J] => A * B) by
  equals (fun A dA => (A * B, dA * B)) =>
    unfold fwdFDeriv; fun_trans

abbrev_fun_trans _matrix (A : R^[I,J]) : fwdFDeriv R (fun B : R^[J,K] => A * B) by
  equals (fun B dB => (A * B, A * dB)) =>
    unfold fwdFDeriv; fun_trans

abbrev_fun_trans _matrix : fwdFDeriv R (fun AB : R^[I,J] × R^[J,K] => AB.1 * AB.2) by
  rw[fwdFDeriv_wrt_prod]; autodiff

abbrev_fun_trans _matrix (B : R^[J,K]) : adjoint R (fun A : R^[I,J] => A * B) by
  equals (fun C => C * Bᵀ) =>
    simp[HMul.hMul]; fun_trans

abbrev_fun_trans _matrix (A : R^[I,J]) : adjoint R (fun B : R^[J,K] => A * B) by
  equals (fun C => Aᵀ * C) =>
    simp[HMul.hMul]; fun_trans

abbrev_fun_trans _matrix : revFDeriv R (fun AB : R^[I,J] × R^[J,K] => AB.1 * AB.2) by
  rw[revFDeriv_wrt_prod]; unfold revFDeriv; autodiff

abbrev_fun_trans _matrix : revFDerivProj R Unit (fun AB : R^[I,J] × R^[J,K] => AB.1 * AB.2) by
  rw[revFDerivProj_wrt_prod]; unfold revFDerivProj; autodiff

abbrev_fun_trans _matrix : revFDerivProjUpdate R Unit (fun AB : R^[I,J] × R^[J,K] => AB.1 * AB.2) by
  rw[revFDerivProjUpdate_wrt_prod]; unfold revFDerivProjUpdate; autodiff
