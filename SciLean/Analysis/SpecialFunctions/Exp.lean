import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.Analysis.Calculus.RevCDeriv
import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Analysis.Calculus.FwdCDeriv
import SciLean.Analysis.Calculus.ContDiff

open ComplexConjugate

namespace SciLean.Scalar

set_option deprecated.oldSectionVars true

variable
  {R C} [Scalar R C] [RealScalar R]
  {W} [Vec C W]
  {U} [SemiInnerProductSpace C U]


----------------------------------------------------------------------------------------------------
-- Exp ---------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

def_fun_prop exp in x with_transitive : Differentiable K by sorry_proof
def_fun_prop exp in x with_transitive : ContDiff K ⊤ by sorry_proof

set_option linter.unusedVariables false in
@[fun_trans]
theorem exp.arg_x.fderiv_rule
    {W} [NormedAddCommGroup W] [NormedSpace C W]
    (x : W → C) (hx : Differentiable C x) :
    fderiv C (fun w => exp (x w))
    =
    fun w => fun dw =>L[C]
      let x'  := x w
      let dx' := fderiv C x w dw
      dx' * exp x' := sorry_proof


@[fun_trans]
theorem exp.arg_x.fwdFDeriv_rule
    {W} [NormedAddCommGroup W] [NormedSpace C W]
    (x : W → C) (hx : Differentiable C x) :
    fwdFDeriv C (fun w => exp (x w))
    =
    fun w dw =>
      let xdx := fwdFDeriv C x w dw
      let y := exp xdx.1
      (y, xdx.2 * y) := by

  unfold fwdFDeriv
  fun_trans


@[fun_trans]
theorem exp.arg_x.revFDeriv_rule
    {W} [NormedAddCommGroup W] [AdjointSpace C W] [CompleteSpace W]
    (x : W → C) (hx : Differentiable C x) :
    revFDeriv C (fun w => exp (x w))
    =
    fun w =>
      let xdx := revFDeriv C x w
      let y := exp xdx.1
      (y,
       fun dy =>
         let s := conj y
         s • xdx.2 dy) := by

  unfold revFDeriv
  fun_trans


set_option linter.unusedVariables false in
@[fun_prop]
theorem exp.arg_x.CDifferentiable_rule
  (x : W → C) (hx : CDifferentiable C x)
  : CDifferentiable C fun w => exp (x w) := sorry_proof

set_option linter.unusedVariables false in
@[fun_trans]
theorem exp.arg_x.ceriv_rule
  (x : W → C) (hx : CDifferentiable C x)
  : cderiv C (fun w => exp (x w))
    =
    fun w dw =>
      let xdx := fwdCDeriv C x w dw
      let e := exp xdx.1
      xdx.2 * e := sorry_proof

@[fun_trans]
theorem exp.arg_x.fwdCDeriv_rule
    (x : W → C) (hx : CDifferentiable C x) :
    fwdCDeriv C (fun w => exp (x w))
    =
    fun w dw =>
      let xdx := fwdCDeriv C x w dw
      let e := exp xdx.1
      (e, xdx.2 * e) := by
  unfold fwdCDeriv; fun_trans; rfl

@[fun_prop]
theorem exp.arg_x.HasAdjDiff_rule
    (x : U → C) (hx : HasAdjDiff C x) :
    HasAdjDiff C (fun u => exp (x u)) := by
  intro x
  constructor
  fun_prop
  fun_trans [fwdCDeriv]; fun_prop

open ComplexConjugate
@[fun_trans]
theorem exp.arg_x.revCDeriv_rule
    (x : U → C) (hx : HasAdjDiff C x) :
    revCDeriv C (fun u => exp (x u))
    =
    fun u =>
      let xdx := revCDeriv C x u
      (exp xdx.1, fun dy => xdx.2 (conj (exp xdx.1) * dy)) := by
  unfold revCDeriv
  fun_trans [fwdCDeriv, smul_push, simp_core]




@[simp, simp_core, exp_push]
theorem exp_zero : exp (0:R) = 1 := sorry_proof
@[simp, simp_core, exp_push]
theorem exp_log (x : R) : exp (log x) = abs x := sorry_proof

@[exp_push]
theorem exp_add (x y : R) : exp (x+y) = exp x * exp y := sorry_proof
@[exp_pull]
theorem mul_exp (x y : R) : exp x * exp y = exp (x+y) := sorry_proof

@[exp_push]
theorem exp_sub (x y : R) : exp (x-y) = exp x / exp y := sorry_proof
@[exp_pull]
theorem div_exp (x y : R) : exp x / exp y = exp (x-y) := sorry_proof

@[exp_push]
theorem exp_inv (x : R) : exp (-x) = (exp x)⁻¹ := sorry_proof
@[exp_pull]
theorem inv_exp (x : R) : (exp x)⁻¹ = exp (-x) := sorry_proof

@[exp_push]
theorem exp_mul (x y : R) : (exp x*y) = (exp x)^y := sorry_proof
@[exp_pull]
theorem pow_exp (x y : R) : (exp x)^y = exp (x*y) := sorry_proof
