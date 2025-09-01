import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.VectorMeasure
import Mathlib.MeasureTheory.Decomposition.Lebesgue
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner

-- import SciLean.Core
import SciLean.Core.FunctionPropositions.Differentiable

open MeasureTheory ENNReal

namespace SciLean.Prob

local notation "∞" => (⊤ : ℕ∞)

variable
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]

/-- Generalized function with domain `X` -/
structure Distribution (X : Type u) where
  action : {Y : Type u} → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → [CompleteSpace Y] → (X → Y) → Y

class DistributionActionNotation (Distrib TestFun : Type _) (Result : outParam <| Type _) where
  action : Distrib → TestFun → Result

export DistributionActionNotation (action)

scoped notation "⟪" f' ", " φ "⟫" => DistributionActionNotation.action f' φ

instance : DistributionActionNotation (Distribution X) (X → Y) Y where
  action := fun f φ => Distribution.action f φ


/-- Prefer `DistributionActionNotation.action` over `Distribution.action` -/
@[simp]
theorem distribution_action_normalize (f : Distribution X) (φ : X → Y) :
    f.action φ = ⟪f, φ⟫ := by rfl

@[simp]
theorem action_mk_apply
    (f : {Y : Type u} → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → [CompleteSpace Y] →  (X → Y) → Y) (φ : X → Y) :
    ⟪Distribution.mk f, φ⟫ = f φ := by rfl

@[ext]
theorem Distribution.ext (x y : Distribution X) :
    (∀ {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] (φ : X → Y), ⟪x,φ⟫ = ⟪y,φ⟫)
    →
    x = y := by

  induction x; induction y; simp only [action_mk_apply, mk.injEq]
  intro h; funext _ _ _ _ φ; apply (h φ)



----------------------------------------------------------------------------------------------------
-- Monadic structure -------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- def dirac (x : X) : Distribution X := fun φ => φ x

instance : Monad Distribution where
  pure := fun x => ⟨fun φ => φ x⟩
  bind := fun x f => ⟨fun φ => ⟪x, fun x' => ⟪(f x'), φ⟫⟫⟩


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

@[simp]
theorem action_bind (x : Distribution X) (f : X → Distribution Y) (φ : Y → W) :
    ⟪x >>= f, φ⟫ = ⟪x, fun x' => ⟪f x', φ⟫⟫ := by rfl


----------------------------------------------------------------------------------------------------
-- Arithmetics -------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

instance : Zero (Distribution X) := ⟨⟨fun _φ => 0⟩⟩
instance : Add (Distribution X) := ⟨fun f g => ⟨fun φ => ⟪f, φ⟫ + ⟪g, φ⟫⟩⟩
instance : Sub (Distribution X) := ⟨fun f g => ⟨fun φ => ⟪f, φ⟫ - ⟪g, φ⟫⟩⟩
noncomputable instance : SMul ℝ (Distribution X) := ⟨fun r f => ⟨fun φ => r • ⟪f, φ⟫⟩⟩



----------------------------------------------------------------------------------------------------
-- Measures as distributions -----------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

open Classical in
@[coe]
noncomputable
def _root_.MeasureTheory.Measure.toDistribution {X} {_ : MeasurableSpace X} (μ : Measure X) :
    Distribution X := ⟨fun φ => ∫ x, φ x ∂μ⟩

noncomputable
instance {X} [TopologicalSpace X] : Coe (@Measure X (borel X)) (Distribution X) := ⟨fun μ => μ.toDistribution⟩


def Distribution.IsMeasure {X} [TopologicalSpace X] (f : Distribution X) : Prop :=
  ∃ (μ : @Measure X (borel X)), ∀ {Y : Type _} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] (φ : X → Y),
      ⟪f, φ⟫ = ∫ x, φ x ∂μ

open Classical
noncomputable
def Distribution.measure {X} [TopologicalSpace X] (f' : Distribution X) : @Measure X (borel X) :=
  if h : f'.IsMeasure then
    choose h
  else
    0

@[simp]
theorem apply_measure_as_distribution  {X} [TopologicalSpace X]  (μ : @Measure X (borel X)) (φ : X → Y) :
     ⟪μ.toDistribution, φ⟫ = ∫ x, φ x ∂μ := by rfl


/- under what conditions is this true??? -/
theorem action_is_integral  {X} [TopologicalSpace X] {Y} [TopologicalSpace Y]
    (x : @Measure X (borel X)) (f : X → @Measure Y (borel Y))
    (φ : Y → Z) (hφ : ∀ x, Integrable φ (f x)) :
    ⟪x.toDistribution >>= (fun x => (f x).toDistribution), φ⟫
    =
    ∫ y, φ y ∂(@Measure.bind _ _ (borel _) (borel _) x f) := by

  simp
  sorry

theorem Distribution.density {X} [TopologicalSpace X] (x y : Distribution X) : X → ℝ≥0∞ := x.measure.rnDeriv y.measure
