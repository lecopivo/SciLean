import SciLean.Core.Rand.Rand
import SciLean.Core.FloatAsReal
import SciLean.Core.Rand.Distributions.Uniform

open MeasureTheory ENNReal BigOperators Finset

namespace SciLean.Rand

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


-- ugh how to deal with empty intervals ?!
open Rand in
instance (a b : R) : UniformRand (Set.Ioo a b) where
  uniform := do
    let x ← uniformI R
    return ⟨a + x * (b - a), sorry_proof⟩

-- ugh how to deal with empty intervals ?!
open Rand in
instance (a b : R) : UniformRand (Set.Ioc a b) where
  uniform := do
    let x ← uniformI R
    return ⟨a + x * (b - a), sorry_proof⟩

-- ugh how to deal with empty intervals ?!
open Rand in
instance (a b : R) : UniformRand (Set.Ico a b) where
  uniform := do
    let x ← uniformI R
    return ⟨a + x * (b - a), sorry_proof⟩

-- ugh how to deal with empty intervals ?!
open Rand in
instance (a b : R) : UniformRand (Set.Icc a b) where
  uniform := do
    let x ← uniformI R
    return ⟨a + x * (b - a), sorry_proof⟩



variable [MeasureSpace R]

@[simp, ftrans_simp]
theorem Set.Ioo_volume (a b : R) (h : a ≤ b) : (volume (Set.Ioo a b)) = Scalar.toENNReal (b - a) := sorry_proof

@[simp, ftrans_simp]
theorem Set.Ioc_volume (a b : R) (h : a ≤ b) : (volume (Set.Ioc a b)) = Scalar.toENNReal (b - a) := sorry_proof

@[simp, ftrans_simp]
theorem Set.Ico_volume (a b : R) (h : a ≤ b) : (volume (Set.Ico a b)) = Scalar.toENNReal (b - a) := sorry_proof

@[simp, ftrans_simp]
theorem Set.Icc_volume (a b : R) (h : a ≤ b) : (volume (Set.Icc a b)) = Scalar.toENNReal (b - a) := sorry_proof
