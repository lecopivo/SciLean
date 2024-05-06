import SciLean.Tactic.RefinedSimp
import SciLean.Tactic.IfPull
import SciLean.Core.FloatAsReal

import SciLean.Core.Integral.HasDerivUnderIntegral
import SciLean.Core.Integral.Substitution
import SciLean.Core.Integral.PlaneDecomposition
import SciLean.Core.Integral.RnDeriv

import Mathlib.Tactic.LiftLets

open Lean Meta

namespace SciLean

open MeasureTheory

variable
  {R : Type} [RealScalar R]
  {W : Type} [Vec R W]
  {X : Type} [SemiHilbert R X] [MeasureSpace X]
  {Y : Type} [Vec R Y] [Module ℝ Y]
  {Z : Type} [Vec R Z] [Module ℝ Z]

set_default_scalar R

variable [MeasureSpace R] [PlainDataType R]

attribute [ftrans_simp] MeasureTheory.Measure.restrict_univ Measure.restrict_singleton

macro "let" i:ident " := " t:term : conv => `(conv| tactic => let $i := $t)
macro "have" i:ident " := " t:term : conv => `(conv| tactic => have $i := $t)




set_option trace.Meta.Tactic.fun_trans true
set_option trace.Meta.Tactic.fun_trans.unify true
set_option trace.Meta.Tactic.fun_trans.step true
set_option trace.Meta.Tactic.fun_trans.discharge true
set_option trace.Meta.Tactic.simp.rewrite true




open Set

set_option profiler true
set_option trace.Meta.Tactic.gtrans true
set_option trace.Meta.Tactic.fun_prop true
-- set_option trace.Meta.Tactic.gtrans.candidates true
-- set_option trace.Meta.Tactic.gtrans.normalize true



#check (∂ (w:=(1:R)), ∫' x in Icc (0:R) 1, if x ≤ w then (1:R) else 0)
  rewrite_by
    fun_trans (config:={zeta:=false}) (disch:=first | assumption | gtrans) only
      [↓ refinedRewritePre, ↑ refinedRewritePost, ftrans_simp, Tactic.lift_lets_simproc]
    autodiff


macro "integral_deriv" : conv =>
  `(conv| fun_trans (config:={zeta:=false}) (disch:=first | assumption | gtrans) only
      [↓ refinedRewritePre, ↑ refinedRewritePost, ftrans_simp, Tactic.lift_lets_simproc,
       scalarGradient, scalarCDeriv])


variable (w' t' : R)

#check (∂ (w:=w'),
          ∫' x in Icc (0:R) 1,
            if x ≤ w then w*x else w + x)
  rewrite_by
    integral_deriv


#check (∂ (w:=w'),
          ∫' x in Icc (0:R) 1,
            if x ≤ w then if 2*w + 3*x ≤ 0 then 5*w*x else 2*w*w*x else w + x)
  rewrite_by
    integral_deriv


#check (∂ (w:=w'),
          ∫' x in Icc (0:R) 1, ∫' y in Icc (0:R) 1,
            if y ≤ w then (1:R) else 0)
  rewrite_by
    integral_deriv


#check (∂ (w:=w'),
          ∫' x in Icc (0:R) 1, ∫' y in Icc (0:R) 1,
            if x ≤ w then (1:R) else 0)
  rewrite_by
    integral_deriv


#check (∂ (w:=w'),
          ∫' x in Icc (0:R) 1, ∫' y in Icc (0:R) 1,
            if x + y + w ≤ 0 then (1:R) else 0)
  rewrite_by
    integral_deriv


#check (∂ t:=t',
          ∫' (xy : R×R) in (Icc 0 1).prod (Icc 0 1),
            if xy.1 + xy.2 ≤ t then xy.1 * xy.2 * t else xy.1 + xy.2 + t)
  rewrite_by
    integral_deriv


#check (∂ t:=t',
          ∫' (xy : R×R) in (Icc 0 1).prod (Icc 0 1),
            if xy.1 ≤ t then
              -if xy.2 ≤ t then (1:R) else 0
            else
              if xy.1 + xy.2 ≤ t then t else t*t)
  rewrite_by
    integral_deriv
    simp (config := {zeta:=false})
