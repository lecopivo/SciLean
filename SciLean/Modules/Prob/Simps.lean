import Mathlib.Control.Random
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Probability.Density

import SciLean.Modules.Prob.SimpAttr

open MeasureTheory ENNReal BigOperators Finset

namespace SciLean.Prob


@[simp]
theorem ENNReal.ofReal_toReal (x : ℝ) : (ENNReal.ofReal x).toReal = x := sorry


variable
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
  {α} [MeasurableSpace α]
  {β} [MeasurableSpace β]


----------------------------------------------------------------------------------------------------
-- Measure bind ------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------




----------------------------------------------------------------------------------------------------
-- Measure and integral theorems -------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[rand_simp,simp]
theorem lower_integral_direc (f : X → ℝ≥0∞) :
    (∫⁻ x', f x' ∂(Measure.dirac x)) = f x := sorry

@[rand_simp,simp]
theorem integral_direc {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X → Y) :
    (∫ x', f x' ∂(Measure.dirac x)) = f x := sorry

@[rand_simp,simp]
theorem dirac_of_set (x : X) (A : Set X) :
    (Measure.dirac x) A = Set.indicator A (fun _ => 1) x := sorry

@[rand_simp,simp]
theorem lower_integral_indicator (c : ℝ≥0∞) (A : Set X) (μ : Measure X) :
    (∫⁻ x, Set.indicator A (fun _ => c) x ∂μ) = c * μ A := sorry

@[rand_simp,simp]
theorem lower_integral_indicator_fun (f : X → ℝ≥0∞) (A : Set X) (μ : Measure X) :
    (∫⁻ x, Set.indicator A f x ∂μ) = (∫⁻ x in A, f x ∂μ) := sorry

@[rand_simp,simp]
theorem lower_integral_indicator_preimage (f : X → Y) (A : Set Y) (μ : Measure X) :
    (∫⁻ x, Set.indicator A (fun _ => 1) (f x) ∂μ) = μ.map f A := sorry



@[rand_simp,simp]
theorem integral_of_add_measure (f : α → X) (μ ν : Measure α) :
    ∫ x, f x ∂(μ + ν) = ∫ x, f x ∂μ + ∫ x, f x ∂ν := sorry


@[rand_simp,simp]
theorem integral_of_dirac (f : α → X) (a : α) :
    ∫ x, f x ∂(Measure.dirac a) = f a := sorry
