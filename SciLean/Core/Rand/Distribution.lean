import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Decomposition.Lebesgue

import SciLean.Core.Objects.Vec
import SciLean.Core.Objects.Scalar
import SciLean.Core.Rand.CIntegral
import SciLean.Util.SorryProof

open MeasureTheory ENNReal

namespace SciLean

local notation "∞" => (⊤ : ℕ∞)

variable
  {R} [RealScalar R]
  {W} [Vec R W] [Module ℝ W]-- [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  {X} [Vec R X] -- [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {Y} [Vec R Y] [Module ℝ Y] -- [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  {Z} [Vec R Z] -- [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]


/-- Generalized function with domain `X`
todo: consider renaming it to GeneralizedFunction X. -/
structure Distribution (X : Type u) where
  /- This should probably be a continuation from `X` to locally convex space `Y`.
  Unfortunatelly mathlib does not have integration of functions with values in locally convex sp.
  Also over what field should the module be? -/
  action : {Y : Type u} → [AddCommGroup Y] → [Module ℝ Y] → (X → Y) → Y

-- class DistributionActionNotation (Distrib TestFun : Type _) (Result : outParam <| Type _) where
--   action : Distrib → TestFun → Result

-- export DistributionActionNotation (action)

scoped notation "⟪" f' ", " φ "⟫" => Distribution.action f' φ

-- instance : DistributionActionNotation (Distribution X) (X → Y) Y where
--   action := fun f φ => Distribution.action f φ


-- /-- Prefer `DistributionActionNotation.action` over `Distribution.action` -/
-- @[simp]
-- theorem distribution_action_normalize (f : Distribution X) (φ : X → Y) :
--     f.action φ = ⟪f, φ⟫ := by rfl

@[simp]
theorem action_mk_apply (f : {Y : Type u} → (X → Y) → Y) (φ : X → Y) :
    ⟪Distribution.mk f, φ⟫ = f φ := by rfl

variable (x : Distribution X) (φ : X → Y)

#check ⟪x,φ⟫

@[ext]
theorem Distribution.ext (x y : Distribution X) :
    (∀ {Y : Type _} [AddCommGroup Y] [Module ℝ Y] (φ : X → Y), ⟪x,φ⟫ = ⟪y,φ⟫)
    →
    x = y := by

  induction x; induction y; simp only [action_mk_apply, mk.injEq]
  intro h; funext; tauto


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

-- instance : Zero (Distribution X) := ⟨⟨fun _φ => 0⟩⟩
-- instance : Add (Distribution X) := ⟨fun f g => ⟨fun φ => ⟪f, φ⟫ + ⟪g, φ⟫⟩⟩
-- instance : Sub (Distribution X) := ⟨fun f g => ⟨fun φ => ⟪f, φ⟫ - ⟪g, φ⟫⟩⟩
-- noncomputable instance : SMul ℝ (Distribution X) := ⟨fun r f => ⟨fun φ => r • ⟪f, φ⟫⟩⟩



----------------------------------------------------------------------------------------------------
-- Measures as distributions -----------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- open Classical in
@[coe]
noncomputable
def _root_.MeasureTheory.Measure.toDistribution {X} {_ : MeasurableSpace X} (μ : Measure X) :
    Distribution X := ⟨fun φ => ∫' x, φ x ∂μ⟩

noncomputable
instance {X} [MeasurableSpace X] : Coe (Measure X) (Distribution X) := ⟨fun μ => μ.toDistribution⟩

-- I'm a bit unsure about this definition
-- For example under what conditions `x.IsMeasure → ∀ x', (f x').IsMeasure → (x >>= f).IsMeasure`
-- I'm a bit affraid that with this definition this might never be true as you can always pick
-- really nasty `φ` to screw up the integral
-- So I think that there has to be some condition on `φ`. Likely they should be required to be test funcions

def Distribution.IsMeasure {X} [MeasurableSpace X] (f : Distribution X) : Prop :=
  ∃ (μ : Measure X), ∀ {Y : Type _} [AddCommGroup Y] [Module ℝ Y] (φ : X → Y),
      ⟪f, φ⟫ = ∫' x, φ x ∂μ

open Classical
noncomputable
def Distribution.measure {X} [MeasurableSpace X] (f' : Distribution X) : Measure X :=
  if h : f'.IsMeasure then
    choose h
  else
    0

-- @[simp]
-- theorem apply_measure_as_distribution  {X} [MeasurableSpace X]  (μ : Measure X) (φ : X → Y) :
--      ⟪μ.toDistribution, φ⟫ = ∫ x, φ x ∂μ := by rfl


/- under what conditions is this true??? -/
-- theorem action_is_integral  {X} [MeasurableSpace X] {Y} [MeasurableSpace Y]
--     (x : Measure X) (f : X → Measure Y)
--     (φ : Y → Z) (hφ : ∀ x, Integrable φ (f x)) :
--     ⟪x.toDistribution >>= (fun x => (f x).toDistribution), φ⟫
--     =
--     ∫ y, φ y ∂(@Measure.bind _ _ _ _ x f) := by
--   sorry_proof

theorem Distribution.density {X} [MeasurableSpace X] (x y : Distribution X) : X → ℝ≥0∞ :=
  x.measure.rnDeriv y.measure
