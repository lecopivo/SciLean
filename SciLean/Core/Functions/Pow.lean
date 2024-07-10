import SciLean.Core.FunctionTransformations
import SciLean.Core.FloatAsReal
-- import SciLean.Core.Meta.GenerateRevDeriv

open ComplexConjugate

namespace SciLean.Scalar

variable
  {R} [RealScalar R]
  {W} [Vec R W]
  {U} [SemiInnerProductSpace R U]



----------------------------------------------------------------------------------------------------
-- Sqrt --------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

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
      let xdx := fwdDeriv R x w dw
      xdx.2 / (2 * sqrt xdx.1) := sorry_proof

@[fun_trans]
theorem sqrt.arg_x.cderiv_rule
    (x : W → R) (hx : CDifferentiable R x) (hw : ∀ w, 0 < x w) :
    cderiv R (fun w => sqrt (x w))
    =
    fun w dw =>
      let xdx := fwdDeriv R x w dw
      xdx.2 / (2 * sqrt xdx.1) := by
  funext x
  fun_trans (disch:=aesop)

@[fun_trans]
theorem sqrt.arg_x.fwdDeriv_rule_at
    (w : W) (x : W → R) (hx : CDifferentiableAt R x w) (hw : 0 < x w) :
    fwdDeriv R (fun w => sqrt (x w)) w
    =
    fun dw =>
      let xdx := fwdDeriv R x w dw
      let x' := sqrt xdx.1
      (x', xdx.2 / (2 * x')) :=
by
  unfold fwdDeriv
  fun_trans (disch:=assumption) [fwdDeriv]

@[fun_trans]
theorem sqrt.arg_x.fwdDeriv_rule
    (x : W → R) (hx : CDifferentiable R x) (hw : ∀ w, 0 < x w) :
    fwdDeriv R (fun w => sqrt (x w))
    =
    fun w dw =>
      let xdx := fwdDeriv R x w dw
      let x' := sqrt xdx.1
      (x', xdx.2 / (2 * x')) :=
by
  unfold fwdDeriv; fun_trans (disch:=assumption) [fwdDeriv]

@[fun_prop]
theorem sqrt.arg_x.HasAdjDiffAt_rule
    (u : U) (x : U → R) (hx : HasAdjDiffAt R x u) (hu : 0 < x u) :
    HasAdjDiffAt R (fun u => sqrt (x u)) u := by
  constructor
  fun_prop (disch:=aesop)
  fun_trans (disch:=aesop) [fwdDeriv]; fun_prop

@[fun_prop]
theorem sqrt.arg_x.HasAdjDiff_rule
    (x : U → R) (hx : HasAdjDiff R x) (hu : ∀ u, 0 < x u) :
    HasAdjDiff R (fun u => sqrt (x u)) := by
  intro u;
  fun_prop (disch:=aesop)

open ComplexConjugate
@[fun_trans]
theorem sqrt.arg_x.revDeriv_rule_at
    (u : U) (x : U → R) (hx : HasAdjDiffAt R x u) (hu : 0 < x u) :
    revDeriv R (fun u => sqrt (x u)) u
    =
    let xdx := revDeriv R x u
    let x' := sqrt xdx.1
    (x', fun dy => xdx.2 (dy / (2 * x'))) := by
  unfold revDeriv
  fun_trans (disch:=aesop) only [fwdDeriv, smul_push, ftrans_simp]
  simp; funext dy; congr
  field_simp [mul_comm]

open ComplexConjugate
@[fun_trans]
theorem sqrt.arg_x.revDeriv_rule
    (x : U → R) (hx : HasAdjDiff R x) (hu : ∀ u, 0 < x u) :
    revDeriv R (fun u => sqrt (x u))
    =
    fun u =>
      let xdx := revDeriv R x u
      let x' := sqrt xdx.1
      (x', fun dy => xdx.2 (dy / (2 * x'))) := by
  funext u
  fun_trans (disch:=aesop) only [fwdDeriv, smul_push, ftrans_simp]
