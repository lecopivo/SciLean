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
@[fun_prop]
theorem log.arg_x.DifferentiableAt_rule
    (w : W) (x : W → R) (hx : DifferentiableAt R x w) (hw : x w ≠ 0) :
    DifferentiableAt R (fun w => log (x w)) w := sorry_proof

@[fun_prop]
theorem log.arg_x.Differentiable_rule
    (x : W → R) (hx : Differentiable R x) (hw : ∀ w, x w ≠ 0) :
    Differentiable R (fun w => log (x w)) := by
  intro x; fun_prop (disch:=aesop)


set_option linter.unusedVariables false in
@[data_synth]
theorem log.arg_x.HasFDerivAt_rule
    (w : W) (x : W → R) {x'} (hx : HasFDerivAt (𝕜:=R) x x' w) (hw : x w ≠ 0) :
    HasFDerivAt (fun w => log (x w))
      (ContinuousLinearMap.mk' R (fun dw =>
        let x := x w
        let dx := x' dw
        dx / abs x) (by fun_prop)) w := sorry_proof

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
  sorry_proof

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
  sorry_proof

end Normed

open Scalar

@[simp, simp_core, log_push]
theorem log_one : log (1:R) = 0 := sorry_proof
@[simp, simp_core, log_push]
theorem log_exp (x : R) : log (exp x) = x := sorry_proof

@[log_push]
theorem log_mul (x y : R) : log (x*y) = log x + log y := sorry_proof
@[log_pull]
theorem add_log (x y : R) : log x + log y = log (x*y) := sorry_proof

@[log_push]
theorem log_div (x y : R) : log (x/y) = log x - log y := sorry_proof
@[log_pull]
theorem sub_log (x y : R) : log x - log y = log (x/y) := sorry_proof

@[log_push]
theorem log_inv (x : R) : log (x⁻¹) = - log x := sorry_proof
@[log_pull]
theorem neg_log (x : R) : - log x = log (x⁻¹) := sorry_proof

@[log_push]
theorem log_pow (x y : R) : log (x^y) = y * log x := sorry_proof
@[log_push]
theorem log_pow_nat (x : R) (n : ℕ) : log (x^n) = n * log x := sorry_proof
@[log_push]
theorem log_pow_int (x : R) (n : ℤ) : log (x^n) = n * log x := sorry_proof
@[log_pull]
theorem mul_log (x y : R) : y * log x = log (x^y) := sorry_proof
@[log_pull]
theorem mul_log' (x y : R) : (log x) * y = log (x^y) := sorry_proof

@[log_push]
theorem log_prod {I} [Fintype I] (f : I → R) : log (∏ i, f i) = ∑ i, log (f i) := sorry_proof
@[log_pull]
theorem sum_log {I} [Fintype I] (f : I → R) : (∑ i, log (f i)) = log (∏ i, f i) := sorry_proof

end Log
