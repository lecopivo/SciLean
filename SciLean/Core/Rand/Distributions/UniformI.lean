import SciLean.Core.Rand.Rand
import SciLean.Core.FloatAsReal

open MeasureTheory ENNReal BigOperators Finset

namespace SciLean.Prob

variable {R} [RealScalar R]


variable (R)
/-- Uniform random number between `0` and `1`. -/
def uniformI : Rand R := {
  spec :=
    erase (⟨fun φ => ∫' x in Set.Icc (0:R) (1:R), φ x ∂sorry⟩) -- todo: add volume to RealScalar
  rand :=
    fun g => do
    let g : StdGen := g.down
    let N := 1000000000000000
    let (n,g) := _root_.randNat g 0 N
    let y := (n : R) / (N : R)
    pure (y, ← ULiftable.up g)
}
variable {R}

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
