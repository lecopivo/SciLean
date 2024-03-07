import SciLean.Core.Rand.Rand
import SciLean.Core.FloatAsReal

open MeasureTheory ENNReal BigOperators Finset

namespace SciLean.Prob

variable {R} [RealScalar R]

instance : LawfulRand (uniformI R) where
  is_measure := sorry_proof
  is_prob    := sorry_proof

-- @[rand_simp,simp]
-- theorem uniformI.pdf (x : R) (_hx : x ∈ Set.Icc 0 1) :
--     (uniformI R).pdf R volume
--     =
--     1 := by sorry_proof

-- theorem uniformI.measure (θ : R) :
--     (uniformI R).ℙ = volume.restrict (Set.Ioo 0 1) :=
--   sorry_proof


variable
  {X} [AddCommGroup X] [Module R X] [Module ℝ X]

-- @[rand_simp,simp]
-- theorem uniformI.integral (θ : R) (f : Bool → X) :
--     ∫' x, f x ∂(uniformI R).ℙ = ∫' x in Set.Ioo 0 1, f x := by
--   simp [rand_simp,uniformI.measure]; sorry_proof

-- theorem uniformI.E (θ : R) (f : Bool → X) :
--     (uniformI R).E f = ∫' x in Set.Ioo 0 1, f x := by
--   simp only [Rand.E_as_cintegral,uniformI.integral]
