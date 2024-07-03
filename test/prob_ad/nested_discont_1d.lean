import SciLean.Core.Integral.HasParamDerivWithJumps
import SciLean.Core.Integral.HasParamFwdDerivWithJumps
import SciLean.Core.Integral.HasParamRevDerivWithJumps
import SciLean.Core.Integral.HasParamDerivWithJumpsCommon
import SciLean.Tactic.LSimp
import SciLean.Tactic.LFunTrans

open SciLean MeasureTheory Set

variable
  {R : Type} [RealScalar R] [MeasureSpace R] [BorelSpace R]

set_default_scalar R

set_option trace.Meta.Tactic.simp.rewrite true
set_option trace.Meta.Tactic.simp.discharge true
set_option trace.Meta.Tactic.simp.unify true

attribute [ftrans_simp ↓] SciLean.ContinuousLinearMap.mk'_eval


@[ftrans_simp]
theorem frontier_setOf_le' {X} [TopologicalSpace X] {R} [RealScalar R] (f g : X → R)
  (hf : Continuous f) (hg : Continuous g) :
  frontier (setOf (no_index fun x => f x ≤ g x))
  =
  {x | f x = g x} := sorry_proof


#check frontier_setOf_le

example (w : R) (a : R) (ha : a ≠ 0) :
    (fderiv R (fun w' =>
      ∫ x in Icc (0:R) 1,
        if x ≤ w' then if w' ≤ a * x then (1:R) else 0 else 0) w 1)
    =
    let ds := if w ∈ Icc 0 1 then if w ≤ a * w then 1 else 0 else 0;
    let w' := a⁻¹ * w
    let ds_1 := if w' ∈ {x | x ≤ w} ∩ Icc 0 1 then -1/(Scalar.abs a) else 0;
    let sf' := ds + ds_1;
    sf' := by

  conv =>
    lhs

    rw[fderiv_under_integral_over_set
           (hf:= by gtrans
                      (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
                      (norm:=lsimp only [ftrans_simp]))
                      (hA := by assume_almost_disjoint)]

    -- for some reason `assumption` tactic fails to apply `ha`
    lautodiff (disch:=first | apply ha | fun_prop (disch:=apply ha)) [inter_assoc]
