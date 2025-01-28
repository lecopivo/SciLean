import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.Analysis.Calculus.RevCDeriv
import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Analysis.Calculus.FwdCDeriv
import SciLean.Analysis.Calculus.ContDiff
import SciLean.Analysis.Calculus.HasRevFDeriv
import SciLean.Meta.GenerateFunTrans
import SciLean.Lean.ToSSA

open ComplexConjugate

namespace SciLean.Scalar

set_option deprecated.oldSectionVars true



----------------------------------------------------------------------------------------------------
-- Exp ---------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

def_fun_prop exp in x with_transitive : Differentiable K by sorry_proof
def_fun_prop exp in x with_transitive : ContDiff K ⊤ by sorry_proof

abbrev_fun_trans exp in x : fderiv K by equals (fun x => fun dx =>L[K] dx • exp x) => sorry_proof
abbrev_fun_trans exp in x : fwdFDeriv K by unfold fwdFDeriv; fun_trans; to_ssa
abbrev_fun_trans exp in x : revFDeriv K by unfold revFDeriv; fun_trans; to_ssa

abbrev_data_synth exp in x (x₀) : (HasFDerivAt (𝕜:=K) · · x₀) by
  apply hasFDerivAt_from_fderiv
  case deriv => conv => rhs; fun_trans
  case diff => dsimp[autoParam]; fun_prop

abbrev_data_synth exp in x : HasRevFDeriv K by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => conv => rhs; to_ssa

abbrev_data_synth exp in x : HasRevFDerivUpdate K by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => conv => rhs; to_ssa

def_fun_prop exp in x with_transitive : HasAdjDiff K by sorry_proof

abbrev_fun_trans exp in x : cderiv K by equals (fun x dx => dx • exp x) => sorry_proof
abbrev_fun_trans exp in x : fwdCDeriv K by unfold fwdCDeriv; fun_trans; to_ssa
abbrev_fun_trans exp in x : revCDeriv K by unfold revCDeriv; fun_trans; to_ssa


variable {R C} [RealScalar R] [Scalar R C]

@[simp, simp_core, exp_push]
theorem exp_zero : exp (0:C) = 1 := sorry_proof
@[simp, simp_core, exp_push]
theorem exp_log (x : R) : exp (log x) = abs x := sorry_proof

@[exp_push]
theorem exp_add (x y : C) : exp (x+y) = exp x * exp y := sorry_proof
@[exp_pull]
theorem mul_exp (x y : C) : exp x * exp y = exp (x+y) := sorry_proof

@[exp_push]
theorem exp_sub (x y : C) : exp (x-y) = exp x / exp y := sorry_proof
@[exp_pull]
theorem div_exp (x y : C) : exp x / exp y = exp (x-y) := sorry_proof

@[exp_push]
theorem exp_inv (x : C) : exp (-x) = (exp x)⁻¹ := sorry_proof
@[exp_pull]
theorem inv_exp (x : C) : (exp x)⁻¹ = exp (-x) := sorry_proof

@[exp_push]
theorem exp_mul (x y : C) : (exp x*y) = (exp x)^y := sorry_proof
@[exp_pull]
theorem pow_exp (x y : C) : (exp x)^y = exp (x*y) := sorry_proof
