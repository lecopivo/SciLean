import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.Analysis.Calculus.RevCDeriv
import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Analysis.Calculus.FwdCDeriv
import SciLean.Analysis.Calculus.HasRevFDeriv
import SciLean.Analysis.Calculus.HasFwdFDeriv

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
@[fun_trans]
theorem log.arg_x.fderiv_rule_at
    (w : W) (x : W → R) (hx : DifferentiableAt R x w) (hw : x w ≠ 0) :
    fderiv R (fun w => log (x w)) w
    =
    ContinuousLinearMap.mk' R (fun dw =>
      let xdx := fwdFDeriv R x w dw
      xdx.2 / abs xdx.1) (by simp[fwdFDeriv]; fun_prop) := sorry_proof

@[fun_trans]
theorem log.arg_x.fderiv_rule
    (x : W → R) (hx : Differentiable R x) (hw : ∀ w, x w ≠ 0) :
    fderiv R (fun w => log (x w))
    =
    fun w => ContinuousLinearMap.mk' R (fun dw =>
      let xdx := fwdFDeriv R x w dw
      xdx.2 / abs xdx.1) (by simp[fwdFDeriv]; fun_prop) := by
  funext x
  fun_trans (disch:=aesop)

@[fun_trans]
theorem log.arg_x.fwdFDeriv_rule_at
    (w : W) (x : W → R) (hx : DifferentiableAt R x w) (hw : x w ≠ 0) :
    fwdFDeriv R (fun w => log (x w)) w
    =
    fun dw =>
      let xdx := fwdFDeriv R x w dw
      let l := log xdx.1
      (l, xdx.2 / abs xdx.1) :=
by
  unfold fwdFDeriv; fun_trans (disch:=assumption); simp[fwdFDeriv]

@[fun_trans]
theorem log.arg_x.fwdFDeriv_rule
    (x : W → R) (hx : Differentiable R x) (hw : ∀ w, x w ≠ 0) :
    fwdFDeriv R (fun w => log (x w))
    =
    fun w dw =>
      let xdx := fwdFDeriv R x w dw
      let l := log xdx.1
      (l, xdx.2 / abs xdx.1) :=
by
  unfold fwdFDeriv; fun_trans (disch:=assumption); simp[fwdFDeriv]

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


open ComplexConjugate
@[fun_trans]
theorem log.arg_x.revFDeriv_rule_at
    (u : U) (x : U → R) (hx : DifferentiableAt R x u) (hu : x u ≠ 0) :
    revFDeriv R (fun u => log (x u)) u
    =
    let xdx := revFDeriv R x u
    (log xdx.1, fun dy => xdx.2 ((abs (x u))⁻¹ * dy)) := by
  unfold revFDeriv
  fun_trans (disch:=assumption) [fwdFDeriv, smul_push, simp_core]

open ComplexConjugate
@[fun_trans]
theorem log.arg_x.revFDeriv_rule
    (x : U → R) (hx : Differentiable R x) (hu : ∀ u, x u ≠ 0) :
    revFDeriv R (fun u => log (x u))
    =
    fun u =>
      let xdx := revFDeriv R x u
      (log xdx.1, fun dy => xdx.2 ((abs (x u))⁻¹ * dy)) := by
  unfold revFDeriv
  fun_trans (disch:=assumption) [fwdFDeriv, smul_push, simp_core]


omit [CompleteSpace U] in
@[data_synth]
theorem log.arg_x.HasRevFDeriv_rule
    (x : U → R) {x'} (hx : HasRevFDeriv R x x') (hu : ∀ u, x u ≠ 0) :
    HasRevFDeriv R (fun u => log (x u))
      (fun u =>
        let' (x,dx) := x' u
        (log x, fun dy =>
          let du := dx (dy / (abs (x)))
          du)) := by
  have ⟨_,_,_,_⟩ := hx.deriv_adjoint
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intro; data_synth (disch:=apply hu)
  case adjoint => intros; dsimp; data_synth
  case simp =>
    funext u;
    have h : (x' u).1 = x u := sorry_proof
    simp[h]

omit [CompleteSpace U] in
@[data_synth]
theorem log.arg_x.HasRevFDerivUpdate_rule
    (x : U → R) {x'} (hx : HasRevFDerivUpdate R x x') (hu : ∀ u, x u ≠ 0) :
    HasRevFDerivUpdate R (fun u => log (x u))
      (fun u =>
        let' (x,dx) := x' u
        (log x, fun dy du =>
          let du := dx (dy / (abs (x))) du
          du)) := by
  have ⟨_,_,_,_⟩ := hx.deriv_adjointUpdate
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intro; data_synth (disch:=apply hu)
  case adjoint => intros; dsimp; data_synth
  case simp =>
    funext u;
    have h : (x' u).1 = x u := sorry_proof
    simp[h]

end Normed


section Convenient

variable
  {W : Type _} [Vec R W]
  {U : Type _} [SemiInnerProductSpace R U]


set_option linter.unusedVariables false in
@[fun_prop]
theorem log.arg_x.CDifferentiableAt_rule
    (w : W) (x : W → R) (hx : CDifferentiableAt R x w) (hw : x w ≠ 0) :
    CDifferentiableAt R (fun w => log (x w)) w := sorry_proof

@[fun_prop]
theorem log.arg_x.CDifferentiable_rule
    (x : W → R) (hx : CDifferentiable R x) (hw : ∀ w, x w ≠ 0) :
    CDifferentiable R (fun w => log (x w)) := by
  intro x; fun_prop (disch:=aesop)

set_option linter.unusedVariables false in
@[fun_trans]
theorem log.arg_x.cderiv_rule_at
    (w : W) (x : W → R) (hx : CDifferentiableAt R x w) (hw : x w ≠ 0) :
    cderiv R (fun w => log (x w)) w
    =
    fun dw =>
      let xdx := fwdCDeriv R x w dw
      xdx.2 / abs xdx.1 := sorry_proof

@[fun_trans]
theorem log.arg_x.cderiv_rule
    (x : W → R) (hx : CDifferentiable R x) (hw : ∀ w, x w ≠ 0) :
    cderiv R (fun w => log (x w))
    =
    fun w dw =>
      let xdx := fwdCDeriv R x w dw
      xdx.2 / abs xdx.1 := by
  funext x
  fun_trans (disch:=aesop)

@[fun_trans]
theorem log.arg_x.fwdCDeriv_rule_at
    (w : W) (x : W → R) (hx : CDifferentiableAt R x w) (hw : x w ≠ 0) :
    fwdCDeriv R (fun w => log (x w)) w
    =
    fun dw =>
      let xdx := fwdCDeriv R x w dw
      let l := log xdx.1
      (l, xdx.2 / abs xdx.1) :=
by
  unfold fwdCDeriv; fun_trans (disch:=assumption); simp[fwdCDeriv]

@[fun_trans]
theorem log.arg_x.fwdCDeriv_rule
    (x : W → R) (hx : CDifferentiable R x) (hw : ∀ w, x w ≠ 0) :
    fwdCDeriv R (fun w => log (x w))
    =
    fun w dw =>
      let xdx := fwdCDeriv R x w dw
      let l := log xdx.1
      (l, xdx.2 / abs xdx.1) :=
by
  unfold fwdCDeriv; fun_trans (disch:=assumption); simp[fwdCDeriv]

@[fun_prop]
theorem log.arg_x.HasAdjDiffAt_rule
    (u : U) (x : U → R) (hx : HasAdjDiffAt R x u) (hu : x u ≠ 0) :
    HasAdjDiffAt R (fun u => log (x u)) u := by
  constructor
  fun_prop (disch:=aesop)
  fun_trans (disch:=aesop) [fwdCDeriv]; fun_prop

@[fun_prop]
theorem log.arg_x.HasAdjDiff_rule
    (x : U → R) (hx : HasAdjDiff R x) (hu : ∀ u, x u ≠ 0) :
    HasAdjDiff R (fun u => log (x u)) := by
  intro u;
  fun_prop (disch:=aesop)

open ComplexConjugate
@[fun_trans]
theorem log.arg_x.revCDeriv_rule_at
    (u : U) (x : U → R) (hx : HasAdjDiffAt R x u) (hu : x u ≠ 0) :
    revCDeriv R (fun u => log (x u)) u
    =
    let xdx := revCDeriv R x u
    (log xdx.1, fun dy => xdx.2 ((abs (x u))⁻¹ * dy)) := by
  unfold revCDeriv
  fun_trans (disch:=assumption) [fwdCDeriv, smul_push, simp_core]

open ComplexConjugate
@[fun_trans]
theorem log.arg_x.revCDeriv_rule
    (x : U → R) (hx : HasAdjDiff R x) (hu : ∀ u, x u ≠ 0) :
    revCDeriv R (fun u => log (x u))
    =
    fun u =>
      let xdx := revCDeriv R x u
      (log xdx.1, fun dy => xdx.2 ((abs (x u))⁻¹ * dy)) := by
  unfold revCDeriv
  fun_trans (disch:=assumption) [fwdCDeriv, smul_push, simp_core]


end Convenient

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
theorem log_prod {I} [IndexType I] (f : I → R) : log (∏ i, f i) = ∑ i, log (f i) := sorry_proof
@[log_pull]
theorem sum_log {I} [IndexType I] (f : I → R) : (∑ i, log (f i)) = log (∏ i, f i) := sorry_proof

end Log
