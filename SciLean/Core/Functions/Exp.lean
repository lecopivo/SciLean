import SciLean.Core.FunctionTransformations
import SciLean.Core.Meta.GenerateRevDeriv

open ComplexConjugate 

namespace SciLean.Scalar

variable 
  {R C} [Scalar R C]
  {W} [Vec C W]
  {U} [SemiInnerProductSpace C U]


--------------------------------------------------------------------------------
-- Exp -------------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem exp.arg_x.IsDifferentiable_rule 
  (x : W → C) (hx : IsDifferentiable C x)
  : IsDifferentiable C fun w => exp (x w) := sorry_proof

@[ftrans]
theorem exp.arg_x.ceriv_rule 
  (x : W → C) (hx : IsDifferentiable C x)
  : cderiv C (fun w => exp (x w))
    =
    fun w dw => 
      let xdx := fwdCDeriv C x w dw
      let e := exp xdx.1
      xdx.2 * e := sorry_proof

@[ftrans]
theorem exp.arg_x.fwdCDeriv_rule 
  (x : W → C) (hx : IsDifferentiable C x)
  : fwdCDeriv C (fun w => exp (x w))
    =
    fun w dw => 
      let xdx := fwdCDeriv C x w dw
      let e := exp xdx.1
      (e, xdx.2 * e) := 
by 
  unfold fwdCDeriv; ftrans; rfl

#generate_revDeriv exp x
  prop_by unfold HasAdjDiff; constructor; fprop; ftrans; fprop
  abbrev trans_by unfold revDeriv; ftrans; ftrans


--------------------------------------------------------------------------------
-- Log -------------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem log.arg_x.IsDifferentiable_rule 
  (x : W → C) (hx : IsDifferentiable C x)
  : IsDifferentiable C fun w => log (x w) := sorry_proof

@[ftrans]
theorem log.arg_x.ceriv_rule 
  (x : W → C) (hx : IsDifferentiable C x)
  : cderiv C (fun w => log (x w))
    =
    fun w dw => 
      let xdx := fwdCDeriv C x w dw
      xdx.2 / xdx.1 := sorry_proof

@[ftrans]
theorem log.arg_x.fwdCDeriv_rule 
  (x : W → C) (hx : IsDifferentiable C x)
  : fwdCDeriv C (fun w => log (x w))
    =
    fun w dw => 
      let xdx := fwdCDeriv C x w dw
      let l := log xdx.1
      (l, xdx.2 / xdx.1) := 
by 
  unfold fwdCDeriv; ftrans; simp[fwdCDeriv]

#generate_revDeriv log x
  prop_by unfold HasAdjDiff; constructor; fprop; ftrans; fprop
  abbrev trans_by unfold revDeriv; ftrans; ftrans

