import SciLean.Core.FunctionTransformations
import SciLean.Core.Meta.GenerateRevDeriv

open ComplexConjugate 

namespace SciLean.Scalar

variable 
  {R C} [Scalar R C]
  {W} [Vec C W]
  {U} [SemiInnerProductSpace C U]


--------------------------------------------------------------------------------
-- Sin -------------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem sin.arg_x.IsDifferentiable_rule 
  (x : W → C) (hx : IsDifferentiable C x)
  : IsDifferentiable C fun w => sin (x w) := sorry_proof

@[ftrans]
theorem sin.arg_x.ceriv_rule 
  (x : W → C) (hx : IsDifferentiable C x)
  : cderiv C (fun w => sin (x w))
    =
    fun w dw => 
      let xdx := fwdCDeriv C x w dw
      let c := cos xdx.1
      xdx.2 * c := sorry_proof

@[ftrans]
theorem sin.arg_x.fwdCDeriv_rule 
  (x : W → C) (hx : IsDifferentiable C x)
  : fwdCDeriv C (fun w => sin (x w))
    =
    fun w dw => 
      let xdx := fwdCDeriv C x w dw
      let s := sin xdx.1
      let c := cos xdx.1
      (s, xdx.2 * c) := 
by 
  unfold fwdCDeriv; ftrans; rfl

#generate_revDeriv sin x
  prop_by unfold HasAdjDiff; constructor; fprop; ftrans; fprop
  abbrev trans_by unfold revDeriv; ftrans; ftrans


--------------------------------------------------------------------------------
-- Cos -------------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem cos.arg_x.IsDifferentiable_rule 
  (x : W → C) (hx : IsDifferentiable C x)
  : IsDifferentiable C fun w => cos (x w) := sorry_proof

@[ftrans]
theorem cos.arg_x.ceriv_rule 
  (x : W → C) (hx : IsDifferentiable C x)
  : cderiv C (fun w => cos (x w))
    =
    fun w dw => 
      let xdx := fwdCDeriv C x w dw
      let s := -sin xdx.1
      xdx.2 * s := sorry_proof

@[ftrans]
theorem cos.arg_x.fwdCDeriv_rule 
  (x : W → C) (hx : IsDifferentiable C x)
  : fwdCDeriv C (fun w => cos (x w))
    =
    fun w dw => 
      let xdx := fwdCDeriv C x w dw
      let s := sin xdx.1
      let c := cos xdx.1
      (c, xdx.2 * -s) := 
by 
  unfold fwdCDeriv; ftrans; rfl

#generate_revDeriv cos x
  prop_by unfold HasAdjDiff; constructor; fprop; ftrans; fprop
  abbrev trans_by unfold revDeriv; ftrans; ftrans


--------------------------------------------------------------------------------
-- Tang -------------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem tanh.arg_x.IsDifferentiable_rule 
  (x : W → C) (hx : IsDifferentiable C x)
  : IsDifferentiable C fun w => tanh (x w) := sorry_proof

@[ftrans]
theorem tanh.arg_x.ceriv_rule 
  (x : W → C) (hx : IsDifferentiable C x)
  : cderiv C (fun w => tanh (x w))
    =
    fun w dw => 
      let xdx := fwdCDeriv C x w dw
      let t := tanh xdx.1
      let dt := 1 - t^2
      xdx.2 * dt := sorry_proof

@[ftrans]
theorem tanh.arg_x.fwdCDeriv_rule 
  (x : W → C) (hx : IsDifferentiable C x)
  : fwdCDeriv C (fun w => tanh (x w))
    =
    fun w dw => 
      let xdx := fwdCDeriv C x w dw
      let t := tanh xdx.1
      let dt := 1-t^2
      (t, xdx.2 * dt) := 
by 
  unfold fwdCDeriv; ftrans; rfl

#generate_revDeriv tanh x
  prop_by unfold HasAdjDiff; constructor; fprop; ftrans; fprop
  abbrev trans_by 
    unfold revDeriv; ftrans; ftrans
    enter [x] 
    -- we just need to replace `tanh x` with `t`, there should be a tactic for it
    -- or common subexpression optimization should do it
    equals (let t := tanh x;
            let dt := 1 - t ^ 2;
            (t, fun y => (starRingEnd K) dt * y)) => rfl


