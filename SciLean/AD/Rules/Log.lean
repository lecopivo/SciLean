module

public import SciLean.AD.Rules.Common

@[expose] public section


open ComplexConjugate

namespace SciLean.Scalar

--------------------------------------------------------------------------------
-- Log -------------------------------------------------------------------------
--------------------------------------------------------------------------------

section Log

variable
  {R : Type _} [RealScalar R]

section Normed

variable
  {W : Type _} [NormedAddCommGroup W] [NormedSpace R W]
  {U : Type _} [NormedAddCommGroup U] [AdjointSpace R U] [CompleteSpace U]

set_option linter.unusedVariables false in
@[data_synth]
theorem log.arg_x.HasFDerivAt_rule
    (w : W) (x : W → R) {x'} (hx : HasFDerivAt (𝕜:=R) x x' w) (hw : x w ≠ 0) :
    HasFDerivAt (fun w => log (x w))
      (ContinuousLinearMap.mk' R (fun dw =>
        let x := x w
        let dx := x' dw
        dx / abs x) (by fun_prop)) w := sorry_proof

set_option linter.unusedVariables false in
@[fun_prop]
theorem log.arg_x.DifferentiableAt_rule
    (w : W) (x : W → R) (hx : DifferentiableAt R x w) (hw : x w ≠ 0) :
    DifferentiableAt R (fun w => log (x w)) w :=
  (log.arg_x.HasFDerivAt_rule w x hx.hasFDerivAt hw).differentiableAt

@[fun_prop]
theorem log.arg_x.Differentiable_rule
    (x : W → R) (hx : Differentiable R x) (hw : ∀ w, x w ≠ 0) :
    Differentiable R (fun w => log (x w)) := by
  intro x; fun_prop (disch:=aesop)

@[data_synth]
theorem log.arg_x.HasFwdFDerivAt_rule
    (x : W → R) {x'} (hx : HasFwdFDeriv R x x') (hw : ∀ w, x w ≠ 0) :
    HasFwdFDeriv R (fun w => log (x w))
      (fun w dw =>
        let' (x,dx) := x' w dw
        let r := log x
        let dr := dx / abs x
        (r, dr)) := by
  have ⟨_,_,_,_⟩ := hx
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intro; data_synth (disch:=aesop)
  case simp => simp_all


omit [CompleteSpace U] in
set_option linter.unusedVariables false in
@[data_synth]
theorem log.arg_x.HasRevFDeriv_rule
    (x : U → R) {x'} (hx : HasRevFDeriv R x x') (hu : ∀ u, x u ≠ 0) :
    HasRevFDeriv R (fun u => log (x u))
      (fun u =>
        let' (x,dx) := x' u
        (log x, fun dy =>
          let du := dx (dy / (abs (x)))
          du)) := by
  obtain ⟨hval, dx, hd, ha⟩ := hx.deriv_adjoint
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
    (df := fun u => (_root_.ContinuousLinearMap.toSpanSingleton R (abs (x u))⁻¹).comp (dx u))
  case deriv =>
    intro u
    refine hasFDerivAt_from_hasFDerivAt (log.arg_x.HasFDerivAt_rule u x (hd u) (hu u)) ?_
    refine _root_.ContinuousLinearMap.ext fun du => ?_
    simp [_root_.ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  case adjoint =>
    intro u
    have h : ⇑((_root_.ContinuousLinearMap.toSpanSingleton R (abs (x u))⁻¹).comp (dx u))
             = fun du => (abs (x u))⁻¹ * (dx u du) := by
      funext du
      simp [_root_.ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]
    rw [h]
    exact HasAdjoint.comp_rule _ _ (ha u) (HMul.hMul.arg_a1.HasAdjoint_simp_rule _)
  case simp =>
    funext u
    simp [hval, div_eq_mul_inv, mul_comm]

omit [CompleteSpace U] in
set_option linter.unusedVariables false in
@[data_synth]
theorem log.arg_x.HasRevFDerivUpdate_rule
    (x : U → R) {x'} (hx : HasRevFDerivUpdate R x x') (hu : ∀ u, x u ≠ 0) :
    HasRevFDerivUpdate R (fun u => log (x u))
      (fun u =>
        let' (x,dx) := x' u
        (log x, fun dy du =>
          let du := dx (dy / (abs (x))) du
          du)) := by
  obtain ⟨hval, dx, hd, ha⟩ := hx.deriv_adjointUpdate
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
    (df := fun u => (_root_.ContinuousLinearMap.toSpanSingleton R (abs (x u))⁻¹).comp (dx u))
  case deriv =>
    intro u
    refine hasFDerivAt_from_hasFDerivAt (log.arg_x.HasFDerivAt_rule u x (hd u) (hu u)) ?_
    refine _root_.ContinuousLinearMap.ext fun du => ?_
    simp [_root_.ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  case adjoint =>
    intro u
    have h : ⇑((_root_.ContinuousLinearMap.toSpanSingleton R (abs (x u))⁻¹).comp (dx u))
             = fun du => (abs (x u))⁻¹ * (dx u du) := by
      funext du
      simp [_root_.ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]
    rw [h]
    exact HMul.hMul.arg_a1.HasAdjointUpdate_comp_rule _ _ (ha u)
  case simp =>
    funext u
    simp [hval, div_eq_mul_inv, mul_comm]

end Normed

open Scalar

@[simp, simp_core, log_push]
theorem log_exp (x : R) : log (exp x) = x := by
  have he := Scalar.exp_def (K:=R) x
  rw [Scalar.toComplex_eq_toReal, Scalar.toComplex_eq_toReal, ← Complex.ofReal_exp] at he
  have h := Scalar.log_def (K:=R) (exp x)
  rw [Scalar.toComplex_eq_toReal, Scalar.toComplex_eq_toReal, he,
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp] at h
  exact Scalar.toReal_injective (by exact_mod_cast h)

@[log_push]
theorem log_mul (x y : R) : log (x*y) = log x + log y := sorry_proof
@[log_pull]
theorem add_log (x y : R) : log x + log y = log (x*y) := (log_mul x y).symm

@[simp, simp_core, log_push]
theorem log_one : log (1:R) = 0 := by
  have h : (0:R) + log (1:R) = log 1 + log 1 := by rw [zero_add, ← log_mul]; norm_num
  exact (add_right_cancel h).symm

/-- `log 0 = 0` — it follows from `log_mul` applied to `0 * 0 = 0`. -/
theorem log_zero : log (0:R) = 0 := by
  have h : log ((0:R)*0) = log (0:R) + log (0:R) := log_mul 0 0
  rw [mul_zero] at h
  have h' : (0:R) + log (0:R) = log (0:R) + log (0:R) := by rw [zero_add]; exact h
  exact (add_right_cancel h').symm

@[log_push]
theorem log_inv (x : R) : log (x⁻¹) = - log x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [inv_zero, log_zero, neg_zero]
  · have h : log x⁻¹ + log x = 0 := by rw [← log_mul, inv_mul_cancel₀ hx, log_one]
    exact eq_neg_of_add_eq_zero_left h
@[log_pull]
theorem neg_log (x : R) : - log x = log (x⁻¹) := (log_inv x).symm

@[log_push]
theorem log_div (x y : R) : log (x/y) = log x - log y := by
  rw [div_eq_mul_inv, log_mul, log_inv, sub_eq_add_neg]
@[log_pull]
theorem sub_log (x y : R) : log x - log y = log (x/y) := (log_div x y).symm

@[log_push]
theorem log_pow (x y : R) : log (x^y) = y * log x := sorry_proof
@[log_push]
theorem log_pow_nat (x : R) (n : ℕ) : log (x^n) = n * log x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, log_mul, ih]; push_cast; ring
@[log_push]
theorem log_pow_int (x : R) (n : ℤ) : log (x^n) = n * log x := by
  cases n using Int.rec with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast, log_pow_nat]; push_cast; ring
  | negSucc n => rw [zpow_negSucc, log_inv, log_pow_nat]; push_cast; ring
@[log_pull]
theorem mul_log (x y : R) : y * log x = log (x^y) := (log_pow x y).symm
@[log_pull]
theorem mul_log' (x y : R) : (log x) * y = log (x^y) := by rw [mul_comm]; exact (log_pow x y).symm

@[log_push]
theorem log_prod {I} [Fintype I] (f : I → R) : log (∏ i, f i) = ∑ i, log (f i) := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, log_mul, ih]
@[log_pull]
theorem sum_log {I} [Fintype I] (f : I → R) : (∑ i, log (f i)) = log (∏ i, f i) := (log_prod f).symm

end Log
