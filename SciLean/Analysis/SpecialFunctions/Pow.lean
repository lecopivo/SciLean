import SciLean.Analysis.Calculus.FwdCDeriv
import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Analysis.Calculus.RevCDeriv
import SciLean.Analysis.Calculus.RevFDeriv

import SciLean.Core.Meta.GenerateFunProp

open ComplexConjugate

namespace SciLean.Scalar

variable
  {R} [RealScalar R]


----------------------------------------------------------------------------------------------------
-- Sqrt --------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section Normed

variable
  {W : Type _} [NormedAddCommGroup W] [NormedSpace R W]
  {U : Type _} [NormedAddCommGroup U] [AdjointSpace R U] [CompleteSpace U]


set_option linter.unusedVariables false in
def_fun_prop with_transitive (x : R) (hx : x ≠ 0) :
    DifferentiableAt R (fun x : R => sqrt x) x by sorry_proof

set_option linter.unusedVariables false in
def_fun_prop with_transitive (x : W → R) (hx : Differentiable R x) (hx' : ∀ w, x w ≠ 0) :
    Differentiable R (fun w => sqrt (x w)) by sorry_proof

set_option linter.unusedVariables false in
@[fun_trans]
theorem sqrt.arg_x.fderiv_rule (x : R) (hx : x ≠ 0) :
  fderiv R sqrt x
  =
  let y := sqrt x
  fun dx =>L[R]
    dx/(2*y) := sorry_proof

set_option linter.unusedVariables false in
@[fun_trans]
theorem sqrt.arg_x.fderiv_rule' (x : W → R) (hx : Differentiable R x) (hx' : ∀ w, x w ≠ 0) :
  fderiv R (fun w => sqrt (x w))
  =
  fun w =>
    let y := sqrt (x w)
    fun dw =>L[R]
      let dx := fderiv R x w dw
      dx/(2*y) := by
  funext w
  fun_trans (disch:=apply hx')

@[fun_trans]
theorem sqrt.arg_x.fwdFDeriv_rule (x : R) (hx : x ≠ 0) :
  fwdFDeriv R sqrt x
  =
  let y := sqrt x
  fun dx =>
    (y,dx/(2*y)) := by unfold fwdFDeriv; fun_trans (disch:=assumption)

@[fun_trans]
theorem sqrt.arg_x.fwdFDeriv_rule' (x : W → R) (hx : Differentiable R x) (hx' : ∀ w, x w ≠ 0) :
  fwdFDeriv R (fun w => sqrt (x w))
  =
  fun w dw =>
    let xdx := fwdFDeriv R x w dw
    let y := sqrt (xdx.1)
    (y,xdx.2/(2*y)) := by
  funext w
  unfold fwdFDeriv
  fun_trans (disch:=assumption)

@[fun_trans]
theorem sqrt.arg_x.revFDeriv_rule (x : R) (hx : x ≠ 0) :
  revFDeriv R sqrt x
  =
  let y := sqrt x
  (y, fun dx => dx/(2*y)) := by unfold revFDeriv; fun_trans (disch:=assumption); funext y; ring

@[fun_trans]
theorem sqrt.arg_x.revFDeriv_rule' (x : U → R) (hx : Differentiable R x) (hx' : ∀ w, x w ≠ 0) :
  revFDeriv R (fun w => sqrt (x w))
  =
  fun w =>
    let xdx := revFDeriv R x w
    let y := sqrt (xdx.1)
    (y,fun dx =>
      let dy := xdx.2 dx
      (2*y)⁻¹ • dy) := by
  funext w
  unfold revFDeriv
  fun_trans (disch:=assumption)


end Normed

section Convenient

variable
  {W} [Vec R W]
  {U} [SemiInnerProductSpace R U]


set_option linter.unusedVariables false in
@[fun_prop]
theorem sqrt.arg_x.CDifferentiableAt_rule
    (w : W) (x : W → R) (hx : CDifferentiableAt R x w) (hw : x w ≠ 0) :
    CDifferentiableAt R (fun w => sqrt (x w)) w := sorry_proof

@[fun_prop]
theorem sqrt.arg_x.CDifferentiable_rule
    (x : W → R) (hx : CDifferentiable R x) (hw : ∀ w, x w ≠ 0) :
    CDifferentiable R (fun w => sqrt (x w)) := by
  intro x; fun_prop (disch:=aesop)

set_option linter.unusedVariables false in
@[fun_trans]
theorem sqrt.arg_x.cderiv_rule_at
    (w : W) (x : W → R) (hx : CDifferentiableAt R x w) (hw : 0 < x w) :
    cderiv R (fun w => sqrt (x w)) w
    =
    fun dw =>
      let xdx := fwdCDeriv R x w dw
      xdx.2 / (2 * sqrt xdx.1) := sorry_proof

@[fun_trans]
theorem sqrt.arg_x.cderiv_rule
    (x : W → R) (hx : CDifferentiable R x) (hw : ∀ w, 0 < x w) :
    cderiv R (fun w => sqrt (x w))
    =
    fun w dw =>
      let xdx := fwdCDeriv R x w dw
      xdx.2 / (2 * sqrt xdx.1) := by
  funext x
  fun_trans (disch:=aesop)

@[fun_trans]
theorem sqrt.arg_x.fwdCDeriv_rule_at
    (w : W) (x : W → R) (hx : CDifferentiableAt R x w) (hw : 0 < x w) :
    fwdCDeriv R (fun w => sqrt (x w)) w
    =
    fun dw =>
      let xdx := fwdCDeriv R x w dw
      let x' := sqrt xdx.1
      (x', xdx.2 / (2 * x')) :=
by
  unfold fwdCDeriv
  fun_trans (disch:=assumption) [fwdCDeriv]

@[fun_trans]
theorem sqrt.arg_x.fwdCDeriv_rule
    (x : W → R) (hx : CDifferentiable R x) (hw : ∀ w, 0 < x w) :
    fwdCDeriv R (fun w => sqrt (x w))
    =
    fun w dw =>
      let xdx := fwdCDeriv R x w dw
      let x' := sqrt xdx.1
      (x', xdx.2 / (2 * x')) :=
by
  unfold fwdCDeriv; fun_trans (disch:=assumption) [fwdCDeriv]

@[fun_prop]
theorem sqrt.arg_x.HasAdjDiffAt_rule
    (u : U) (x : U → R) (hx : HasAdjDiffAt R x u) (hu : 0 < x u) :
    HasAdjDiffAt R (fun u => sqrt (x u)) u := by
  constructor
  fun_prop (disch:=aesop)
  fun_trans (disch:=aesop) [fwdCDeriv]; fun_prop

@[fun_prop]
theorem sqrt.arg_x.HasAdjDiff_rule
    (x : U → R) (hx : HasAdjDiff R x) (hu : ∀ u, 0 < x u) :
    HasAdjDiff R (fun u => sqrt (x u)) := by
  intro u;
  fun_prop (disch:=aesop)

open ComplexConjugate
@[fun_trans]
theorem sqrt.arg_x.revCDeriv_rule_at
    (u : U) (x : U → R) (hx : HasAdjDiffAt R x u) (hu : 0 < x u) :
    revCDeriv R (fun u => sqrt (x u)) u
    =
    let xdx := revCDeriv R x u
    let x' := sqrt xdx.1
    (x', fun dy => xdx.2 (dy / (2 * x'))) := by
  unfold revCDeriv
  fun_trans (disch:=aesop) only [fwdCDeriv, smul_push, ftrans_simp]
  simp; funext dy; congr
  field_simp [mul_comm]

open ComplexConjugate
@[fun_trans]
theorem sqrt.arg_x.revCDeriv_rule
    (x : U → R) (hx : HasAdjDiff R x) (hu : ∀ u, 0 < x u) :
    revCDeriv R (fun u => sqrt (x u))
    =
    fun u =>
      let xdx := revCDeriv R x u
      let x' := sqrt xdx.1
      (x', fun dy => xdx.2 (dy / (2 * x'))) := by
  funext u
  fun_trans (disch:=aesop) only [fwdCDeriv, smul_push, ftrans_simp]

end Convenient
