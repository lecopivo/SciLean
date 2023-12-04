import SciLean.Core
import SciLean.Data.DataArray
import SciLean.Data.Prod
import Mathlib

namespace SciLean.ML

variable 
  {R : Type} [RealScalar R] [PlainDataType R]

set_default_scalar R

def softMax
  {ι} [Index ι] (r : R) (x : R^ι) : R^ι := 
  let wx := Function.repeatIdx (init:=((0:R),x)) 
    fun (i : ι) (w,x) => 
      let xi := x[i]
      let xi' := Scalar.exp (r*xi)
      (w + xi', setElem x i (xi * xi'))
  -- have : ∀ x :R, x ≠ 0 := by sorry_proof
  wx.2

@[fprop]
theorem Scalar.exp.arg_x.HasAdjDiff_rule 
  {R K} [Scalar R K] {W} [SemiInnerProductSpace K W]
  (x : W → K) (hx : HasAdjDiff K x)
  : HasAdjDiff K (fun w => Scalar.exp (x w)) := by sorry_proof


-- set_option trace.Meta.Tactic.fprop.discharge true 
-- set_option trace.Meta.Tactic.fprop.step true 
-- set_option trace.Meta.Tactic.fprop.apply true 
-- set_option trace.Meta.Tactic.fprop.rewrite true
-- set_option trace.Meta.Tactic.fprop.unify true
set_option trace.Meta.Tactic.ftrans.step true
set_option trace.Meta.Tactic.simp.discharge true
-- #generate_revDeriv softMax r x
--   prop_by unfold softMax; sorry_proof --fprop
--   trans_by unfold softMax; ftrans
