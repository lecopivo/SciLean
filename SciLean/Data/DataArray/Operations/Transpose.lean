import SciLean.Data.DataArray.Operations.Diag
import SciLean.Data.DataArray.Operations.Vecmul
import SciLean.Data.DataArray.Operations.Matmul

namespace SciLean

open DataArrayN

def_fun_prop transpose in A
  with_transitive
  [RealScalar R] : IsContinuousLinearMap R

#generate_linear_map_simps DataArrayN.transpose.arg_A.IsLinearMap_rule


abbrev_fun_trans transpose in A [RealScalar R] : fderiv R by autodiff

abbrev_fun_trans transpose in A [RealScalar R] : fwdFDeriv R by autodiff

abbrev_fun_trans transpose in A [RealScalar R] : adjoint R by
  equals (fun B => B.transpose) =>
    funext x
    apply AdjointSpace.ext_inner_left R
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[DataArrayN.inner_def,Function.HasUncurry.uncurry,
         DataArrayN.transpose,sum_prod_eq_sum_sum]
    rw[sum_swap]

abbrev_fun_trans transpose in A [RealScalar R] : revFDeriv R by unfold revFDeriv; autodiff



variable
  {I : Type} [IndexType I]
  {J : Type} [IndexType J]
  {R : Type} [RealScalar R] [PlainDataType R]

set_default_scalar R

variable (A : R^[I,J]) (x y : R^[I]) (u v : R^[J])

omit [RealScalar R] in
@[simp, simp_core]
theorem transpose_transpose : Aᵀᵀ = A := by ext i; cases i; simp[transpose]

-- TODO: move this
@[sum_pull]
theorem ArrayType.ofFn.arg_f.sum_pull (f : I → J → R) : ⊞ i => ∑ j, f i j = ∑ j, ⊞ i => f i j := by
  ext
  simp

-- TODO: move this
@[sum_pull]
theorem ArrayType.get.arg_cont.sum_pull {X} [AddCommGroup X] [ArrayType Cont I X] (i : I)
  (f : J → Cont) : ArrayType.get (∑ j, f j) i = ∑ j, ArrayType.get (f j) i := sorry_proof

theorem inner_transpose_right : ⟪x, A*v⟫ = ⟪Aᵀ*x, v⟫ := by
  rw[← adjoint_inner_left _ (by fun_prop)]
  fun_trans

theorem inner_transpose_left : ⟪A*u, y⟫ = ⟪u, Aᵀ*y⟫ := by
  rw[← adjoint_inner_right _ (by fun_prop)]
  fun_trans


-- TODO: remove simp from this!
#check ArrayType.sum_ofFn
--set_option trace.Meta.Tactic.simp.unify true in

theorem inner_AAT_right : ⟪x, A*(Aᵀ*y)⟫ = ⟪Aᵀ*x,Aᵀ*y⟫ := by
  rw[inner_transpose_right]
theorem inner_AAT_letft : ⟪A*(Aᵀ*x), y⟫ = ⟪Aᵀ*x,Aᵀ*y⟫ := by
  rw[inner_transpose_left]

theorem inner_ATA_right : ⟪u, Aᵀ*(A*v)⟫ = ⟪A*u,A*v⟫ := by
  rw[inner_transpose_right]
  simp
theorem inner_ATA_letft : ⟪Aᵀ*(A*u), v⟫ = ⟪A*u,A*v⟫ := by
  rw[inner_transpose_left]
  simp
