import SciLean.Data.DataArray.Operations.Softmax
import SciLean.Analysis.SpecialFunctions.Log

namespace SciLean.DataArrayN

open Scalar

variable
  {R : Type} [RealScalar R] [PlainDataType R]
  {I : Type} [IndexType I]

set_default_scalar R

theorem logsumexp_def (x : R^[I]) :
    logsumexp x = Scalar.log (∑ i, Scalar.exp (x[i])) := by
  unfold logsumexp
  simp only [exp_push]
  sorry_proof

def_fun_prop logsumexp in x : Differentiable R by
  simp_rw[logsumexp_def]
  intro x
  have : ∑ i, Scalar.exp x[i] ≠ 0 := sorry_proof
  fun_prop (disch:=dsimp; assumption)

abbrev_fun_trans DataArrayN.logsumexp in x : fderiv R by
  equals (fun x => fun dx =>L[R]
           let x' := softmax x
           ⟪dx, x'⟫[R]) =>

    simp_rw[logsumexp_def]
    funext x
    ext dx
    have hw : ∑ i, Scalar.exp x[i] ≠ 0 := sorry_proof
    fun_trans (disch:=dsimp; assumption) [multiply,inner_def]
    have h : Scalar.abs ( ∑ i, (Scalar.exp x[i], dx[i] * Scalar.exp x[i])).1
             =
             ∑ i, Scalar.exp x[i] := sorry_proof
    have h' : (∑ i, (Scalar.exp x[i], dx[i] * Scalar.exp x[i])).2
              =
              (∑ i, dx[i] * Scalar.exp x[i]) := sorry_proof
    simp_rw[h,h']
    simp_rw[softmax_def]
    simp
    -- almost done, just need to pull `w` out of the sum
    sorry_proof

abbrev_fun_trans logsumexp in x : fwdFDeriv R by
  unfold fwdFDeriv
  autodiff

abbrev_fun_trans logsumexp in x [DecidableEq I] : revFDeriv R by
  unfold revFDeriv
  autodiff

abbrev_fun_trans logsumexp in x [DecidableEq I] : revFDerivProj R Unit by
  unfold revFDerivProj
  autodiff

abbrev_fun_trans logsumexp in x [DecidableEq I] : revFDerivProjUpdate R Unit by
  unfold revFDerivProjUpdate
  autodiff


@[log_push]
theorem log_sum_exp (x : I → R) :
    Scalar.log (∑ i, Scalar.exp (x i)) = (⊞ i => x i).logsumexp := by
  simp [logsumexp_def]
