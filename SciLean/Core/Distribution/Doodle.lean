import SciLean.Core.Distribution.ParametricDistribDeriv
import SciLean.Core.Distribution.SurfaceDirac
import SciLean.Core.Distribution.Eval
-- import SciLean.Core.Integral.Substitution
-- import SciLean.Core.Integral.ParametricInverse
-- import SciLean.Core.Integral.Frontier

import SciLean.Core.FunctionTransformations.Preimage

import SciLean.Tactic.IfPull

import SciLean.Core

import SciLean.Util.RewriteBy

open MeasureTheory Set BigOperators

namespace SciLean

variable
  {R} [RealScalar R] [MeasureSpace R]
  {W} [SemiHilbert R W]
  {X} [SemiHilbert R X]
  {Y} [SemiHilbert R Y] -- [Module ℝ Y]
  {Z} [SemiHilbert R Z] -- [Module ℝ Z]

set_default_scalar R

attribute [ftrans_simp]
  FiniteDimensional.finrank_self FiniteDimensional.finrank_prod
  not_le ite_mul mul_ite mul_neg mul_one setOf_eq_eq_singleton
  Finset.card_singleton PUnit.default_eq_unit Finset.univ_unique Finset.sum_const
  preimage_id'
  mem_setOf_eq mem_ite_empty_right mem_inter_iff mem_ite_empty_right mem_univ mem_Ioo
  and_true
  bind_pure bind_assoc pure_bind


variable [Module ℝ Z] [MeasureSpace X] [Module ℝ Y]


-- set_option profiler true in
-- set_option trace.Meta.Tactic.fun_prop true in
-- set_option trace.Meta.Tactic.fun_trans true in
-- set_option trace.Meta.Tactic.simp.rewrite true in
def foo4 (t' : R) :=
  derive_random_approx
    (∂ (t:=t'), ∫' (x : R) in Ioo 0 1, ∫' (y : R) in Ioo 0 1, if x ≤ t then x*y*t else x+y+t)
  by
    fun_trans only [scalarGradient, scalarCDeriv]
    simp only [Tactic.if_pull]
    fun_trans only [scalarGradient, scalarCDeriv]
    simp only [ftrans_simp]
    simp only [toDistrib_pull,restrict_pull]
    simp only [restrict_push]
    simp only [ftrans_simp,restrict_push]
    simp (disch:=sorry) only [action_push, ftrans_simp, restrict_push]

    conv =>
      enter[2]
      simp only [distrib_eval,ftrans_simp]
      simp only [Tactic.if_pull]
      simp (disch:=sorry) only [action_push, ftrans_simp, restrict_push]
      simp only [distrib_eval,ftrans_simp]

    simp only [distrib_eval,ftrans_simp]

    rand_pull_E
    simp (disch:=sorry) only [ftrans_simp]
