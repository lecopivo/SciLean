import SciLean.Core.Integral.Common

import SciLean.Tactic.LetEnter
import SciLean.Tactic.LetUtils

open SciLean MeasureTheory Set

variable
  {R : Type} [RealScalar R] [MeasureSpace R]

set_default_scalar R

#check _root_.MeasureTheory.Measure.restrict_restrict
#check SciLean.Measure.restrict_restrict

-- set_option trace.Meta.Tactic.simp.discharge true
-- set_option trace.Meta.Tactic.fun_trans.discharge true
set_option trace.Meta.Tactic.simp.rewrite true
set_option trace.Meta.Tactic.fun_trans.rewrite true

example (w : R) :
    (∂ w':=w,
      ∫' x in Icc (0:R) 1,
        if x ≤ w' then if x + w' ≤ 0 then (1:R) else 0 else 0)
    =
    let ds := if w ∈ Icc 0 1 then if w + w ≤ 0 then 1 else 0 else 0;
    let ds_1 := -if -w ∈ Icc 0 1 ∩ {x | x ≤ w} then 1 else 0;
    let sf' := ds_1 + ds;
    sf' := by

  conv =>
    lhs

    unfold scalarCDeriv

    simp (config := {zeta:=false,singlePass:=false}) (disch:=gtrans (disch:=fun_prop)) only [Tactic.lift_lets_simproc,cintegral.arg_f.cderiv_rule']


    simp (config := {zeta:=false,singlePass:=false}) (disch:=gtrans (disch:=fun_prop))
      only [restrictToFrontier_eq_restrictToLevelSet,Tactic.lift_lets_simproc,
            SciLean.Measure.restrict_restrict,
            vectorIntegral_volume_restrict_restrictToLevelSet_eq_cintegral]


    fun_trans (config := {zeta:=false}) only [scalarCDeriv,scalarGradient]


    simp (config := {zeta:=false,singlePass:=true}) (disch:=gtrans (disch:=fun_prop)) only [surfaceIntegral_inter_parametrization]


    simp (config := {zeta:=false,singlePass:=false})  only [ftrans_simp, Tactic.lift_lets_simproc]


    fun_trans (config:={zeta:=false}) only []

    -- fun_trans (config:={zeta:=false,singlePass:=true}) (disch:=sorry_proof) only [ftrans_simp,Tactic.lift_lets_simproc, scalarGradient, scalarCDeriv]
    -- simp (config:={zeta:=false,failIfUnchanged:=false}) only [ftrans_simp,Tactic.lift_lets_simproc]

    -- simp (config:={zeta:=false,singlePass:=false})  only
    --       [Set.mem_Icc,Set.mem_inter_iff]

    simp (config:={zeta:=false,singlePass:=true}) only
          [ftrans_simp, Tactic.lift_lets_simproc, scalarGradient, scalarCDeriv]

    simp (config:={zeta:=false,singlePass:=true}) only
          [ftrans_simp, Tactic.lift_lets_simproc, scalarGradient, scalarCDeriv]

    autodiff



#check Nat

set_option pp.notation false
set_option pp.all true
example (y : ℝ) (P : ℝ → ℝ → Prop) [∀ x y, Decidable (P x y)] :
    (if (let x := -y; P x y) then y + 0 else y)
    =
    sorry := by

  conv =>
    lhs
    simp (config:={zeta:=false}) only [Tactic.lift_lets_simproc]

    simp (config:={zeta:=false})


#check Set.mem_inter_iff
