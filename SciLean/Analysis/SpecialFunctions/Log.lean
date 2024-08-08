import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.Analysis.Calculus.RevCDeriv
import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Analysis.Calculus.FwdCDeriv

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


@[simp, simp_core]
theorem log_one : Scalar.log (1:R) = 0 := sorry_proof
@[simp, simp_core]
theorem log_exp (x : R) : Scalar.log (Scalar.exp x) = x := sorry_proof
theorem log_mul (x y : R) : Scalar.log (x*y) = Scalar.log x + Scalar.log y := sorry_proof
theorem log_div (x y : R) : Scalar.log (x/y) = Scalar.log x - Scalar.log y := sorry_proof
theorem log_inv (x : R) : Scalar.log x⁻¹ = - Scalar.log x := sorry_proof

end Log
