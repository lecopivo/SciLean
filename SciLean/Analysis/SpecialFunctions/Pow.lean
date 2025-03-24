import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Analysis.Calculus.RevFDeriv

import SciLean.Meta.GenerateFunProp

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
