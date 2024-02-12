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


noncomputable
def uniform (a b : ℝ) : Distribution ℝ := fun φ => (b-a)⁻¹ * ∫ x in Set.uIcc a b, φ x

noncomputable
def duniform (a b da db : ℝ) : Distribution ℝ :=
  fun φ => (b - a)⁻¹ * (db * φ b - da * φ a - (db - da) * (b - a)⁻¹ * ∫ x in Set.uIcc a b, φ x)

noncomputable
def fduniform (a b da db : ℝ) : FDistribution ℝ := {
  val := uniform a b
  dval := duniform a b da db
}

-- I think we migh be able to remove the condition `a x ≠ b x`
-- @[fprop]
theorem uniform.differentiableAt (a b : X → ℝ) (φ : ℝ → ℝ) (x : X) (hab : a x ≠ b x)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hφa : ContinuousAt φ (a x)) (hφb : ContinuousAt φ (b x)) : -- also integrability condition
    DifferentiableAt ℝ (fun x => uniform (a x) (b x) φ) x := by dsimp[uniform]; sorry



-- @[fprop]
theorem uniform.bind._arg_xf.differentiableAt (a b : X → ℝ) (f : X → ℝ → Distribution Z) (φ : Z → ℝ) (x : X) (hab : a x ≠ b x)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    -- TODO: weaken 'hf' such that we still need `ha` and `hb`
    (hf : DifferentiableUnderIntegralAt (fun x y => f x y φ) (fun x' => volume.restrict (Set.uIcc (a x') (b x'))) x) :
    DifferentiableAt ℝ (fun x => bind (uniform (a x) (b x)) (f x) φ) x := by

  simp[uniform,bind]
  apply DifferentiableAt.mul
  . sorry
  . apply hf.diff




@[simp]
theorem uniform.distribDeriv_comp
    (a b : X → ℝ) (x dx : X) (φ : ℝ → ℝ) (hab : a x ≠ b x)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hφa : ContinuousAt φ (a x)) (hφb : ContinuousAt φ (b x))
    /- integrability condition on φ -/:
    distribDeriv (fun x : X => uniform (a x) (b x)) x dx φ
    =
    let a' := a x
    let da := fderiv ℝ a x dx
    let b' := b x
    let db := fderiv ℝ b x dx
    duniform a' b' da db φ := by

  simp[uniform,duniform,bind,distribDeriv]
  rw[fderiv_mul (by sorry) (by sorry)]

  sorry


@[simp]
theorem uniform.bind.arg_xf.distribDeriv_rule
    (a b : X → ℝ) (f : X → ℝ → Distribution Z) (x dx) (φ : Z → ℝ) (hab : a x ≠ b x)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    -- TODO: weaken 'hf' such that we still need `ha` and `hb`
    (hf : DifferentiableUnderIntegralAt (fun x y => f x y φ) (fun x' => volume.restrict (Set.uIcc (a x') (b x'))) x) :
    distribDeriv (fun x' => (uniform (a x') (b x')) >>= (f x')) x dx φ
    =
    let a' := a x
    let da := fderiv ℝ a x dx
    let b' := b x
    let db := fderiv ℝ b x dx
    bind (duniform a' b' da db) (f x ·) φ
    +
    (uniform a' b') (fun y => distribDeriv (f · y) x dx φ) := by

  simp [distribDeriv, uniform, duniform, bind]
  rw[fderiv_mul (by sorry) (by sorry)]

  sorry


@[simp]
theorem uniform.distribFwdDeriv_comp
    (a b : X → ℝ) (x dx : X) (φ : ℝ → ℝ×ℝ) (hab : a x ≠ b x)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hφa : ContinuousAt φ (a x)) (hφb : ContinuousAt φ (b x))
    /- integrability condition on φ -/:
    distribFwdDeriv (fun x : X => uniform (a x) (b x)) x dx φ
    =
    let ada := fwdFDeriv ℝ a x dx
    let bdb := fwdFDeriv ℝ b x dx
    fduniform ada.1 bdb.1 ada.2 bdb.2 φ := by

  unfold distribFwdDeriv
  -- set up `fprop` for ContinuousAt
  simp (disch := first | assumption | sorry) only [FDistribution_apply, distribDeriv_comp]
  rfl



@[simp]
theorem uniform.bind.arg_xf.distribFwdDeriv_rule
    (a b : X → ℝ) (f : X → ℝ → Distribution Z) (x dx) (φ : Z → ℝ×ℝ) (hab : a x ≠ b x)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    -- TODO: weaken 'hf' such that we still need `ha` and `hb`
    (hf : DifferentiableUnderIntegralAt (fun x y => f x y (fun x => (φ x).1)) (fun x' => volume.restrict (Set.uIcc (a x') (b x'))) x) :
    distribFwdDeriv (fun x' => bind (uniform (a x') (b x')) (f x')) x dx φ
    =
    let ada := fwdFDeriv ℝ a x dx
    let bdb := fwdFDeriv ℝ b x dx
    (fduniform ada.1 bdb.1 ada.2 bdb.2) (fun y => distribFwdDeriv (f · y) x dx φ) := by

  unfold distribFwdDeriv fduniform fwdFDeriv
  simp (disch := first | assumption | sorry) only [FDistribution_apply, distribDeriv_rule, bind, Pi.add_apply, bind]
  simp
  sorry -- linearity of uniform in `φ`
