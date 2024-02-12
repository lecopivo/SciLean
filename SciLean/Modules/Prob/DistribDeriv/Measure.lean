import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul

import SciLean.Modules.Prob.DistribDeriv.DistribDeriv
import SciLean.Modules.Prob.DistribDeriv.DistribFwdDeriv
import SciLean.Modules.Prob.DerivUnderIntegralSign

namespace SciLean.Prob

variable
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [MeasurableSpace Z]


open MeasureTheory

theorem Measure.toDistribution.arg_μ.DifferentiableAt_rule (μ : X → Measure Y) (φ : Y → W) (x : X)
    (hφ : DifferentiableUnderIntegralAt (fun _ y => φ y) μ x) :
    DifferentiableAt ℝ (fun x => ⟪(μ x).toDistribution, φ⟫) x := by

  simp only [apply_measure_as_distribution]
  apply hφ.diff


theorem measure.bind._arg_xf.differentiableAt (μ : X → Measure Y) (f : X → Y → Distribution Z) (φ : Z → W) (x : X)
    (hf : DifferentiableUnderIntegralAt (fun x y => ⟪f x y, φ⟫) μ x) :
    DifferentiableAt ℝ (fun x => ⟪(μ x).toDistribution >>= (f x), φ⟫) x := by

  simp
  apply hf.diff


-- I think this is unnecessary once `fun_prop` support's custom function coercions
@[simp ↓]
theorem measure.distribDeriv_comp
    (f : X → Y) (μ : Y → Measure Z) (x dx : X) (φ : Z → W)
    (hf : DifferentiableAt ℝ f x)
    (hφ : DifferentiableUnderIntegralAt (fun _ y => φ y) μ (f x)) :
    ⟪distribDeriv (fun x' => (μ (f x')).toDistribution) x dx, φ⟫
    =
    let y := f x
    let dy := fderiv ℝ f x dx
    ⟪distribDeriv (fun y => (μ y).toDistribution) y dy, φ⟫ := by

  simp [distribDeriv]
  rw [fderiv.comp_rule_at ℝ (fun y => ∫ (x : Z), φ x ∂(μ y)) f x hφ.diff hf]
  dsimp


@[simp ↓]
theorem measure.bind.arg_xf.distribDeriv_rule
    (μ : X → Measure Y) (f : X → Y → Distribution Z) (x dx) (φ : Z → W)
    (hf : DifferentiableUnderIntegralAt (fun x y => ⟪f x y, φ⟫) μ x) :
    ⟪distribDeriv (fun x' => (μ x').toDistribution >>= (f x')) x dx, φ⟫
    =
    ⟪(distribDeriv (fun x => (μ x).toDistribution) x dx) >>= (f x ·), φ⟫
    +
    ⟪(μ x).toDistribution, fun y => ⟪distribDeriv (f · y) x dx, φ⟫⟫ := by

  simp[distribDeriv]
  rw [deriv_under_integral_sign hf]


@[simp ↓]
theorem measure.distribFwdDeriv_comp
    (f : X → Y) (μ : Y → Measure Z) (x dx : X) (φ : Z → W×W)
    (hf : DifferentiableAt ℝ f x)
    (hφ : DifferentiableUnderIntegralAt (fun x y => φ y) μ (f x)) :
    ⟪distribFwdDeriv (fun x : X => (μ (f x)).toDistribution) x dx, φ⟫
    =
    let ydy := fwdFDeriv ℝ f x dx
    ⟪distribFwdDeriv (fun x => (μ x).toDistribution) ydy.1 ydy.2, φ⟫ := by

  have h : DifferentiableUnderIntegralAt (fun x y => (φ y).1) μ (f x) := sorry

  simp only [distribFwdDeriv, fdaction_mk_apply, apply_measure_as_distribution,
    fwdFDeriv, differentiableAt_id', Prod.mk.injEq, add_left_inj, true_and]
  rw[measure.distribDeriv_comp]
  apply hf
  apply h


@[simp ↓]
theorem measure.bind.arg_xf.distribFwdDeriv_rule
    (μ : X → Measure Y) (f : X → Y → Distribution Z) (x dx) (φ : Z → W×W)
    (hf : DifferentiableUnderIntegralAt (fun x y => ⟪f x y, φ⟫) μ x) :
    ⟪distribFwdDeriv (fun x' => (μ x').toDistribution >>= (f x')) x dx, φ⟫
    =
    ⟪distribFwdDeriv (fun x' => (μ x').toDistribution) x dx, fun y => ⟪distribFwdDeriv (f · y) x dx, φ⟫⟫ := by

  have h  : Integrable (fun x_1 => ⟪distribDeriv (fun x => f x x_1) x dx, fun x => (φ x).1⟫) (μ x) := sorry
  have h' : Integrable (fun x_1 => ⟪f x x_1, fun x => (φ x).2⟫) (μ x) := sorry
  have h'' : DifferentiableUnderIntegralAt (fun x y => ⟪f x y, fun x => (φ x).1⟫) (fun x' => μ x') x := sorry

  simp [distribFwdDeriv,fwdFDeriv]
  rw[measure.bind.arg_xf.distribDeriv_rule]
  . simp only [action_bind, differentiableAt_id', apply_measure_as_distribution]
    rw [integral_add h h']
    .simp[add_assoc]
  . apply h''
