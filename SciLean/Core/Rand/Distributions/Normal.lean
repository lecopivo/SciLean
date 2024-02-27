import SciLean.Core.Rand.Rand
import SciLean.Core.FloatAsReal
import SciLean.Core.Rand.Distributions.UniformI

import SciLean.Core.Rand.Tactic

open MeasureTheory ENNReal Finset

namespace SciLean.Prob

variable {R} [RealScalar R]


variable (R)


def generateNormalV1 : Rand R := do
  return (← go 12 0) - 6
where
  go (n : Nat) (sum : R) : Rand R := do
    match n with
    | 0 => pure sum
    | n+1 => go n (sum + (← uniformI R))


open Scalar in
def generateNormalV2 : Rand R := do
  let u ← uniformI R
  let v ← uniformI R
  let pi : R := 3.14159265359
  return sqrt (-2*log u) * cos (2*pi*v)


-- generateUniformV1 is much slower then generateUniformV2. I'm expecting this is due to the
-- value boxing inside of `_root_.Rand`
-- #eval show IO Unit from do
--   timeit "version 1" (print_mean_variance (generateUniformV1 (R:=Float)) 10000 "")
--   timeit "version 2" (print_mean_variance (generateUniformV2 (R:=Float)) 10000 "")


/-- Uniform random number between `0` and `1`. -/
def normal : Rand R := {
  spec := erase sorry -- (⟨fun φ => ∫' x in Set.Icc (0:R) (1:R), (Scalar.toReal (Scalar.exp x)) •  φ x ∂sorry⟩)
  rand := (generateNormalV2 R).rand
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
