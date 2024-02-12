import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.VectorMeasure
import Mathlib.MeasureTheory.Decomposition.Lebesgue
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner

import SciLean.Core
import SciLean.Core.FunctionPropositions.Differentiable

open MeasureTheory ENNReal

namespace SciLean.Prob

local notation "∞" => (⊤ : ℕ∞)

variable
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [MeasurableSpace Z]

abbrev VectorDistribution (X : Type u) := {Y : Type u} → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → (X → Y) → Y

----------------------------------------------------------------------------------------------------
-- Monadic structure -------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


instance : Monad VectorDistribution where
  pure := fun x _ _ _ φ => φ x
  bind := fun x f _ _ _ φ => x (fun x' => (f x') φ)


instance : LawfulMonad VectorDistribution where
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

-- variable [Add Y] [Sub Y] [Zero Y] [SMul ℝ Y]
instance : Zero (VectorDistribution X) := ⟨fun _φ => 0⟩
instance : Add (VectorDistribution X) := ⟨fun f g _ _ _ φ => f φ + g φ⟩
instance : Sub (VectorDistribution X) := ⟨fun f g _ _ _ φ => f φ - g φ⟩
noncomputable instance : SMul ℝ (VectorDistribution X) := ⟨fun r f _ _ _ φ => r • f φ⟩


----------------------------------------------------------------------------------------------------
-- Measures as VectorDistributions -----------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- open Classical in
-- noncomputable
-- def _root_.MeasureTheory.Measure.toVectorDistribution (μ : VectorMeasure X Y) : VectorDistribution X Y := fun φ =>
--   if Integrable φ μ then
--     ∫ x, φ x ∂μ
--   else
--     0


-- def VectorDistribution.IsMeasure (f : VectorDistribution X Y) : Prop :=
--   ∃ (μ : Measure X),
--     ∀ φ, f φ = μ.toVectorDistribution φ

-- open Classical
-- noncomputable
-- def VectorDistribution.measure (f' : VectorDistribution X Y) : VectorMeasure X Y :=
--   if h : f'.IsMeasure then
--     choose h
--   else
--     0


noncomputable
def distribDeriv
    (f : X → VectorDistribution Y) (x dx : X) : VectorDistribution Y :=
  fun φ => fderiv ℝ (fun x' => (f x') φ) x dx
