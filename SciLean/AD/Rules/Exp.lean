module

public import SciLean.AD.Rules.Common

@[expose] public section


open ComplexConjugate

namespace SciLean.Scalar

set_option deprecated.oldSectionVars true
set_option linter.unusedTactic false
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

abbrev_data_synth exp in x : HasFwdFDeriv K by hasFwdFDeriv_from_def => simp; to_ssa
abbrev_data_synth exp in x : HasRevFDeriv K by hasRevFDeriv_from_def => simp; to_ssa
abbrev_data_synth exp in x : HasRevFDerivUpdate K by hasRevFDerivUpdate_from_def => simp; to_ssa


variable {R C} [RealScalar R] [Scalar R C]

@[simp, simp_core, exp_push]
theorem exp_zero : exp (0:C) = 1 := sorry_proof
@[simp, simp_core, exp_push]
theorem exp_log (x : R) : exp (log x) = abs x := sorry_proof

@[exp_push]
theorem exp_add (x y : C) : exp (x+y) = exp x * exp y := sorry_proof
@[exp_pull]
theorem mul_exp (x y : C) : exp x * exp y = exp (x+y) := (exp_add x y).symm

@[exp_push]
theorem exp_inv (x : C) : exp (-x) = (exp x)⁻¹ := by
  have h : exp (-x) * exp x = 1 := by rw [← exp_add]; simp
  exact eq_inv_of_mul_eq_one_left h
@[exp_pull]
theorem inv_exp (x : C) : (exp x)⁻¹ = exp (-x) := (exp_inv x).symm

@[exp_push]
theorem exp_sub (x y : C) : exp (x-y) = exp x / exp y := by
  rw [sub_eq_add_neg, exp_add, exp_inv, div_eq_mul_inv]
@[exp_pull]
theorem div_exp (x y : C) : exp x / exp y = exp (x-y) := (exp_sub x y).symm

-- The following two statements are false and are therefore commented out:
--
--   @[exp_push]
--   theorem exp_mul (x y : C) : (exp x*y) = (exp x)^y := sorry_proof
--   @[exp_pull]
--   theorem pow_exp (x y : C) : (exp x)^y = exp (x*y) := sorry_proof
--
-- `exp x*y` parses as `exp x * y` (application binds tighter than `*`), so the first one claims
-- `exp x * y = (exp x)^y`, which fails for `y = 0`, see `not_forall_exp_mul_complex`. The second
-- one is false over the complex numbers because complex powers are defined through a branch of
-- the logarithm, see `not_forall_pow_exp_complex`. Both hold for real scalars and are restated
-- for those below.

/-- The statement of `exp_mul`, as it is parsed, fails for the complex numbers. -/
theorem not_forall_exp_mul_complex : ¬ (∀ (x y : ℂ), exp x * y = exp x ^ y) := by
  intro h
  have h0 := h 0 0
  rw [show ((exp (0:ℂ)) ^ (0:ℂ)) = (Complex.exp 0) ^ (0:ℂ) from rfl,
      Complex.cpow_zero, mul_zero] at h0
  exact zero_ne_one h0

/-- The statement of `pow_exp` fails for the complex numbers, e.g. for `x = 2πi` and `y = 1/2`. -/
theorem not_forall_pow_exp_complex : ¬ (∀ (x y : ℂ), exp x ^ y = exp (x*y)) := by
  intro h
  have h0 := h (2*(Real.pi:ℂ)*Complex.I) (1/2)
  have e1 : exp (2*(Real.pi:ℂ)*Complex.I) = 1 := Complex.exp_two_pi_mul_I
  have e2 : (2*(Real.pi:ℂ)*Complex.I*(1/2)) = (Real.pi:ℂ)*Complex.I := by ring
  rw [e1, e2, Complex.one_cpow,
      show exp ((Real.pi:ℂ)*Complex.I) = Complex.exp ((Real.pi:ℂ)*Complex.I) from rfl,
      Complex.exp_pi_mul_I] at h0
  norm_num at h0

/-- Intended form of `exp_mul`, stated for real scalars where it is true. -/
@[exp_push]
theorem exp_mul (x y : R) : exp (x*y) = (exp x)^y := by
  have h : ∀ z : R, Scalar.toReal R (exp z) = Real.exp (Scalar.toReal R z) := fun z => by
    have h := Scalar.exp_def (K:=R) z
    rw [Scalar.toComplex_eq_toReal, Scalar.toComplex_eq_toReal, ← Complex.ofReal_exp] at h
    exact_mod_cast h
  apply Scalar.toReal_injective
  rw [Scalar.toReal_rpow, h, h, ← Real.exp_mul, Scalar.toReal_mul]
@[exp_pull]
theorem pow_exp (x y : R) : (exp x)^y = exp (x*y) := (exp_mul x y).symm
