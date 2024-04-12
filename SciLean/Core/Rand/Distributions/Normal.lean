import SciLean.Core.Rand.Rand
import SciLean.Core.FloatAsReal
import SciLean.Core.Rand.Distributions.UniformI

import SciLean.Core.Functions.Gaussian

import SciLean.Core.Rand.Tactic

open MeasureTheory ENNReal Finset

namespace SciLean.Rand

variable {R} [RealScalar R] [MeasureSpace R]

open Scalar in
def boxMuller (u v : R) : R×R :=
  let tau : R := 2 * RealScalar.pi
  let r := sqrt (-2*log u)
  let θ := tau*v
  (r * cos θ, r * sin θ)

variable (R)

private def generateNormalV1 : Rand R := do
  return (← go 12 0) - 6
where
  go (n : Nat) (sum : R) : Rand R := do
    match n with
    | 0 => pure sum
    | n+1 => go n (sum + (← uniformI R))

open Scalar RealScalar in
private def generateNormalV2 : Rand R := do
  let u ← uniformI R
  let v ← uniformI R
  return sqrt (-2*log u) * cos (2*(pi:R)*v)
variable {R}


/-- Normal random variable with mean `μ` and standard deviation `σ`. -/
def normal (μ σ : R)  : Rand R := {
  spec := erase (fun φ => ∫' x, φ x * (Scalar.toReal R (gaussian μ σ x)))
  rand := do
    let x ← (generateNormalV2 R).rand
    return σ * x + μ
}

instance (μ σ : R) : LawfulRand (normal μ σ) where
  is_measure := sorry_proof
  is_prob    := sorry_proof

@[simp,ftrans_simp]
theorem normal.pdf (μ σ : R) :
    (normal μ σ).pdf R volume
    =
    gaussian μ σ := sorry_proof


@[simp,ftrans_simp]
theorem normal.map_add_right (μ σ : R) (θ : R) :
    (normal μ σ).map (fun x => x + θ)
    =
    (normal (μ+θ) σ) := sorry_proof

@[simp,ftrans_simp]
theorem normal.map_add_left (μ σ : R) (θ : R) :
    (normal μ σ).map (fun x => θ + x)
    =
    (normal (θ + μ) σ) := sorry_proof

@[simp,ftrans_simp]
theorem normal.map_sub_right (μ σ : R) (θ : R) :
    (normal μ σ).map (fun x => x - θ)
    =
    (normal (μ-θ) σ) := sorry_proof
