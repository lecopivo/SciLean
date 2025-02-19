import SciLean.Data.VectorType.Operations.Exp
import SciLean.Data.VectorType.Operations.Dot
import SciLean.Data.VectorType.Operations.Sum
import SciLean.Data.VectorType.Operations.Mul
import SciLean.Analysis.SpecialFunctions.Log

namespace SciLean

open VectorType
section Simps

variable
  {X : Type*} {n : Type u} {R :  Type*}
  {_ : RealScalar R} {_ : IndexType n} [VectorType.Base X n R] [Dense X]

theorem VectorType.logsumexp_spec (x : X) :
  VectorType.logsumexp x
  =
  if 0 < size n then
    Scalar.log (sum (exp x))
  else
    0 := sorry_proof

end Simps

-- differentiable
def_fun_prop logsumexp in x with_transitive [InjectiveGetElem X n] : Differentiable R by
  -- -- this is causing timeout for some reason
  -- simp only [VectorType.logsumexp_spec]
  -- have h : ∀ (w : X), VectorType.sum (VectorType.exp w) ≠ 0 := sorry_proof
  -- fun_prop (disch:=sorry_proof)
  sorry_proof

-- fderiv
abbrev_fun_trans logsumexp in x [InjectiveGetElem X n] : fderiv R by
  equals (fun x => fun dx =>L[R]
           let x' := VectorType.softmax x
           ⟪dx, x'⟫[R]) =>
    sorry_proof

abbrev_data_synth logsumexp in x [InjectiveGetElem X n] (x₀) : (HasFDerivAt (𝕜:=R) · · x₀) by
  apply hasFDerivAt_from_fderiv
  case deriv => conv => rhs; fun_trans; simp[vector_optimize]
  case diff => dsimp[autoParam]; fun_prop

-- forward AD
abbrev_fun_trans logsumexp in x [InjectiveGetElem X n] : fwdFDeriv R by
  unfold fwdFDeriv
  fun_trans; to_ssa

-- reverse AD
abbrev_fun_trans logsumexp in x [InjectiveGetElem X n] : revFDeriv R by
  unfold revFDeriv
  fun_trans; to_ssa

abbrev_data_synth logsumexp in x [InjectiveGetElem X n] : HasRevFDeriv R by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => conv => rhs; simp; to_ssa

abbrev_data_synth logsumexp in x [InjectiveGetElem X n] : HasRevFDerivUpdate R by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => conv => rhs; simp[vector_optimize]; to_ssa; to_ssa; lsimp
