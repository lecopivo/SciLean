import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic

import SciLean.Core.FunctionTransformations
import SciLean.Modules.Prob.DRand

namespace SciLean.Prob

open MeasureTheory ENNReal BigOperators Finset


/-- I think this should effectively say that the theorem `deriv_measure_under_integral` holds.

That should be easy to verify for dirac measure.
For other random variables we will like battle with integrability conditions. -/
opaque RandDifferentiable {X} [NormedAddCommGroup X] [NormedSpace ℝ X] {Y} [MeasurableSpace Y]
    (f : X → Rand Y) : Prop


section RandDeriv


 -- Probalby I should make sure that we are getting borel spaces
variable
  {R} [RealScalar R]
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace R W] [MeasurableSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace R W] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedSpace R W] [MeasurableSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedSpace R W] [MeasurableSpace Z]
  {α} [MeasurableSpace α]
  {β} [MeasurableSpace β]


-- todo: add condition that `φ` is a test function
--       the definition of test function should admit `Z` to be discrete space or vector space
@[rand_simp]
theorem deriv_measure_under_integral (f : Y → Rand Z) (g : X → Y) (φ : Z → ℝ)
    (hf : RandDifferentiable f) (hg : Differentiable ℝ g) :
    fderiv ℝ (fun x' : X => ∫ (z : Z), φ z ∂↑(f (g x')).μ) x dx
    =
    fderiv ℝ (fun x' => ∫ (z : Z), φ z ∂(f x').μ) (g x) (fderiv ℝ g x dx) := sorry


----------------------------------------------------------------------------------------------------
-- Lambda and Monadic Rules ------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[rand_simp,simp]
theorem randDeriv_const (a : Rand α) :
    randDeriv (fun _ : W => a)
    =
    fun w dw => 0 := by

  funext w dw
  apply DRand.ext
  intro φ
  simp only [randDeriv, fderiv_const, Pi.zero_apply,
             ContinuousLinearMap.zero_apply, DRand.action_zero]


@[rand_simp,simp]
theorem randDeriv_comp (f : Y → Rand Z) (g : X → Y)
    (hf : RandDifferentiable f) (hg : Differentiable ℝ g) :
    randDeriv (fun x : X => (f (g x)))
    =
    fun x dx =>
      let ydy := fwdFDeriv ℝ g x dx
      randDeriv f ydy.1 ydy.2 := by

  funext x dx
  unfold fwdFDeriv
  apply DRand.ext; intro φ
  simp (disch:=first | assumption | apply differentiable_id')
    [randDeriv, deriv_measure_under_integral, fderiv_id', ContinuousLinearMap.coe_id', id_eq]


@[rand_simp,simp]
theorem Rand.pure.arg_x.randDeriv_rule (x : W → X) (hx : Differentiable ℝ x) :
    randDeriv (fun w => Rand.pure (x w))
    =
    fun w dw => dpure (x w) (fderiv ℝ x w dw) := by

  funext w dw
  apply DRand.ext; intro φ
  simp (disch:=first | assumption | sorry) only
    [randDeriv, pure, Erased.out_mk, integral_dirac', dpure]
  have h := @fderiv.comp ℝ _ _ _ _ _ _ _ _ _ _ x w φ sorry (hx w)
  unfold Function.comp at h
  rw[h]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]


@[rand_simp,simp]
theorem Rand.bind.arg_xf.randDeriv_rule (x : W → Rand α) (f : W → α → Rand β)
    (hx : RandDifferentiable x) (hf : ∀ x, RandDifferentiable (f · x)) :
    randDeriv (fun w => (x w).bind (f w ·))
    =
    fun w dw => (randDeriv x w dw).bindDR (f w · )
                +
                (x w).bindRD (fun x => randDeriv (f · x) w dw) := by

  funext w dw
  apply DRand.ext; intro φ
  simp only [randDeriv, rand_simp, DRand.bindDR, bindRD, E]
  simp (disch:=sorry) only [integral_bind]
  sorry


----------------------------------------------------------------------------------------------------
-- Other Rules -------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[rand_simp,simp]
theorem ite.arg_tf.randDeriv_rule {c} [Decidable c] (t f : W → Rand α) :
    randDeriv (fun w => if c then (t w) else (f w))
    =
    fun w dw => if c then randDeriv t w dw else randDeriv f w dw := by

  funext w dw
  if h : c then simp [h] else simp [h]
