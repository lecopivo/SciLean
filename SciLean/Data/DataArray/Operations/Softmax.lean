import SciLean.Data.DataArray.Operations.Multiply
import SciLean.Data.DataArray.Operations.Outerprod
import SciLean.Analysis.SpecialFunctions.Exp

namespace SciLean.DataArrayN

open  Scalar


section Missing
@[fun_prop]
theorem HDiv.hDiv.arg_a0a1.Differentiable_rule {R : Type*} [RCLike R] {x : R×R} (hx : x.2 ≠ 0) :
    DifferentiableAt R (fun x : R×R => x.1 / x.2) x := sorry

end Missing

variable
  {R : Type} [RealScalar R] [PlainDataType R]
  {I : Type} [IndexType I]

set_default_scalar R

theorem softmax_def (x : R^[I]) :
    softmax x
    =
    let w := ∑ i, Scalar.exp (x[i])
    ⊞ i => Scalar.exp (x[i]) / w := sorry_proof

def_fun_prop softmax in x : Differentiable R by
  simp[softmax_def]
  intro x
  have : ∑ i, Scalar.exp x[i] ≠ 0 := sorry_proof
  fun_prop (disch:=dsimp; assumption)


abbrev_fun_trans DataArrayN.softmax in x : fderiv R by
  equals (fun x => fun dx =>L[R]
           let x' := softmax x
           x'.multiply dx - ⟪dx, x'⟫[R] • x') =>

    simp[softmax_def]
    funext x
    ext dx i
    have h : ∑ i, Scalar.exp x[i] ≠ 0 := sorry_proof
    fun_trans (disch:=dsimp; assumption) [multiply,inner_def]
    revert h
    generalize (∑ i, Scalar.exp x[i]) = w -- make folowing algebra easier
    -- almost done, just need to pull `w` out of the sum and call field_simp
    sorry_proof

abbrev_fun_trans softmax in x : fwdFDeriv R by
  unfold fwdFDeriv
  autodiff

abbrev_fun_trans softmax in x [DecidableEq I] : revFDeriv R by
  unfold revFDeriv
  autodiff

abbrev_fun_trans softmax in x [DecidableEq I] : revFDerivProj R Unit by
  unfold revFDerivProj
  autodiff

abbrev_fun_trans softmax in x [DecidableEq I] : revFDerivProjUpdate R Unit by
  unfold revFDerivProjUpdate
  autodiff
