import SciLean.Core.Distribution.ParametricDistribDeriv
import SciLean.Core.Distribution.SurfaceDirac
import SciLean.Core.Distribution.Eval
-- import SciLean.Core.Integral.Substitution
-- import SciLean.Core.Integral.ParametricInverse
-- import SciLean.Core.Integral.Frontier
-- import SciLean.Core.Integral.MovingDomain

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

variable [MeasurableSpace X]

-- @[fun_prop]
-- theorem cintegral.arg_f.CDifferentiable_rule' (f : W → X → Y) (μ : Measure X)
--     (hf : ∀ x, CDifferentiable R (f · x)) :
--     CDifferentiable R (fun w => ∫' x, f w x ∂μ) := sorry_proof

-- @[fun_prop]
-- theorem cintegral.arg_f.CDifferentiable_rule''' (f : W → X → Y) (μ : Measure X)
--     (hf : ∀ x, CDifferentiable R (f · x)) :
--     CDifferentiable R (fun w => ∫' x, f w x ∂μ) := by fun_prop


@[fun_prop]
theorem cintegral.arg_f.CDifferentiable_rule'' (f g : W → X → Y) (μ : Measure X)
    (c : W → X → Prop) [∀ w x, Decidable (c w x)]
    (hf : CDifferentiable R (fun w => ∫' x in {x' | c w x'}, f w x ∂μ))
    (hg : CDifferentiable R (fun w => ∫' x in {x' | ¬c w x'}, g w x ∂μ)) :
    CDifferentiable R (fun w => ∫' x, if c w x then f w x else g w x ∂μ) := sorry_proof


-- WARNING!!! We need some condition on `s` such that this is true!!!
-- @[fun_prop]
theorem cintegral.arg_f.CDifferentiable_rule''' (f : W → X → Y) (μ : Measure X)
    (s : W → Set X) (hf : ∀ x, CDifferentiable R (f · x)) :
    CDifferentiable R (fun w => ∫' x in s w, f w x ∂μ) := sorry_proof

set_option trace.Meta.Tactic.fun_prop true in
example (x : R) : CDifferentiable R fun t : R => ∫' (y : R) in Ioo 0 1, if y ≤ t then x*y*t else x+y+t := by
  fun_prop (disch:=sorry)

#check moving_volume_differentiable

set_option trace.Meta.Tactic.fun_prop true in
example : CDifferentiable R fun (w : R) => ∫' x_1 in {x' | x' ≤ w}, x * x_1 * w := by
  fun_prop (disch:=sorry)

-- set_option profiler true in
set_option trace.Meta.Tactic.fun_prop true in
set_option trace.Meta.Tactic.fun_trans true in
-- set_option trace.Meta.Tactic.simp.rewrite true in
def foo4 (t' : R) :=
  derive_random_approx
    (∂ (t:=t'), ∫' (x : R) in Ioo 0 1, ∫' (y : R) in Ioo 0 1, if y ≤ t then x*y*t else x+y+t)
  by
    fun_trans (disch:=sorry) only [scalarGradient, scalarCDeriv]
    simp only [ftrans_simp]
    simp only [toDistrib_pull,restrict_pull]
    simp only [restrict_push]
    simp only [ftrans_simp,restrict_push]
    simp (disch:=sorry) only [action_push, ftrans_simp, restrict_push]
    simp only [distrib_eval,ftrans_simp]
    rand_pull_E
    simp (disch:=sorry) only [ftrans_simp]


-- set_option profiler true in
set_option trace.Meta.Tactic.fun_prop true in
set_option trace.Meta.Tactic.fun_trans true in
-- set_option trace.Meta.Tactic.simp.rewrite true in
def foo5 (t' : R) :=
  derive_random_approx
    (∂ (t:=t'), ∫' (x : R) in Ioo 0 1, Scalar.sqrt (∫' (y : R) in Ioo 0 1, if y ≤ t then x*y*t else x+y+t))
  by
    fun_trans (disch:=sorry) only [scalarGradient, scalarCDeriv, fwdDeriv]
    simp only [ftrans_simp]
    simp only [toDistrib_pull,restrict_pull]
    simp only [restrict_push]
    simp only [ftrans_simp,restrict_push]
    simp (disch:=sorry) only [action_push, ftrans_simp, restrict_push]
    simp only [distrib_eval,ftrans_simp]
    rand_pull_E
    simp (disch:=sorry) only [ftrans_simp]
