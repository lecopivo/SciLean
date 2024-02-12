import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.VectorMeasure
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner

import SciLean.Core
import SciLean.Core.FunctionPropositions.Differentiable

open MeasureTheory

namespace SciLean.Prob

local notation "∞" => (⊤ : ℕ∞)

variable
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [MeasurableSpace Z]

abbrev Distribution (X) := (X → ℝ) → ℝ


----------------------------------------------------------------------------------------------------
-- Monadic structure -------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

def dirac (x : X) : Distribution X := fun φ => φ x

instance : Monad Distribution where
  pure := dirac
  bind := fun x f φ => x (fun x' => (f x') φ)

instance : LawfulMonad Distribution where
  bind_pure_comp := by intros; rfl
  bind_map       := by intros; rfl
  pure_bind      := by intros; rfl
  bind_assoc     := by intros; rfl
  map_const      := by intros; rfl
  id_map         := by intros; rfl
  seqLeft_eq     := by intros; rfl
  seqRight_eq    := by intros; rfl
  pure_seq       := by intros; rfl



----------------------------------------------------------------------------------------------------
-- Arithmetics -------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

instance : Zero (Distribution X) := ⟨fun _φ => 0⟩
instance : Add (Distribution X) := ⟨fun f g φ => f φ + g φ⟩
instance : Sub (Distribution X) := ⟨fun f g φ => f φ - g φ⟩
noncomputable instance : SMul ℝ (Distribution X) := ⟨fun r f φ => r • f φ⟩


----------------------------------------------------------------------------------------------------
-- Measures as distributions -----------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

open Classical in
noncomputable
def _root_.MeasureTheory.Measure.toDistribution (μ : Measure X) : Distribution X := fun φ =>
  if Integrable φ μ then
    ∫ x, φ x ∂μ
  else
    0


def Distribution.IsMeasure (f : Distribution X) : Prop :=
  ∃ (μ : Measure X),
    ∀ φ, μ.toDistribution φ = ∫ x, φ x ∂μ

open Classical
noncomputable
def Distribution.measure (f' : Distribution X) : Measure X :=
  if h : f'.IsMeasure then
    choose h
  else
    0

def Distribution.IsSignedMeasure (f : Distribution X) : Prop :=
  -- Use SignedMeasure but I'm not sure how to write the integral then
  ∃ (μpos μneg : Measure X),
    (IsFiniteMeasure μpos ∧ IsFiniteMeasure μneg) ∧
    ∀ φ, f φ = ∫ x, φ x ∂μpos - ∫ x, φ x ∂μneg

open Classical
noncomputable
def Distribution.signedMeasure (f' : Distribution X) : SignedMeasure X :=
  if h : f'.IsSignedMeasure then
    let μpos := choose h
    let μneg := choose (choose_spec h)
    have ⟨_,_⟩ := (choose_spec (choose_spec h)).1
    μpos.toSignedMeasure - μneg.toSignedMeasure
  else
    0


@[simp]
theorem apply_measure_as_distribution (μ : Measure X) (φ : X → ℝ) :
     μ.toDistribution φ = ∫ x, φ x ∂μ := by

  simp[Measure.toDistribution, integral, (inferInstance : CompleteSpace ℝ)]
  intro h'
  if h : Integrable φ μ then
    contradiction
  else
    simp [h]
