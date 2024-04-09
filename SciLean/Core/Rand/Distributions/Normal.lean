import SciLean.Core.Rand.Rand
import SciLean.Core.FloatAsReal
import SciLean.Core.Rand.Distributions.UniformI

import SciLean.Core.Rand.Tactic

open MeasureTheory ENNReal Finset

namespace SciLean.Rand

variable {R} [RealScalar R]


open Scalar in
def boxMuller (u v : R) : R×R :=
  let tau : R := 2 * RealScalar.pi
  let r := sqrt (-2*log u)
  let θ := tau*v
  (r * cos θ, r * sin θ)


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
def normal (μ σ : R)  : Rand R := {
  spec := erase sorry -- (⟨fun φ => ∫' x in Set.Icc (0:R) (1:R), (Scalar.toReal (Scalar.exp x)) •  φ x ∂sorry⟩)
  rand := do
    let x ← (generateNormalV2 R).rand
    return σ * x + μ
}


variable {R} [MeasureSpace R]


-- TODO: Move to file with basic scalar functions
open Scalar RealScalar in
def gaussian (μ σ x : R) : R :=
  let x' := (x - μ) / σ
  1/(σ*sqrt (2*(pi : R))) * exp (- x'^2/2)

-- open Scalar in
-- @[simp, ftrans_simp]
-- theorem log_gaussian (μ σ x : R) :
--     log (gaussian μ σ x)
--     =
--     let x' := (x - μ) / σ
--     (- x'^2/2) - log σ + log (2*RealScalar.pi) := sorry_proof

instance : LawfulRand (normal R μ σ) where
  is_measure := sorry_proof
  is_prob    := sorry_proof

@[rand_simp,simp,ftrans_simp]
theorem normal.pdf (μ σ : R) :
    (normal R μ σ).pdf R volume
    =
    gaussian μ σ := sorry_proof


@[rand_simp,simp,ftrans_simp]
theorem normal.map_add_right (μ σ : R) (θ : R) :
    (normal R μ σ).map (fun x => x + θ)
    =
    (normal R (μ+θ) σ) := sorry_proof

@[rand_simp,simp,ftrans_simp]
theorem normal.map_add_left (μ σ : R) (θ : R) :
    (normal R μ σ).map (fun x => θ + x)
    =
    (normal R (θ + μ) σ) := sorry_proof

@[rand_simp,simp,ftrans_simp]
theorem normal.map_sub_right (μ σ : R) (θ : R) :
    (normal R μ σ).map (fun x => x - θ)
    =
    (normal R (μ-θ) σ) := sorry_proof



-- variable
--   {X} [AddCommGroup X] [Module R X] [Module ℝ X]

-- -- @[rand_simp,simp]
-- -- theorem uniformI.integral (θ : R) (f : Bool → X) :
-- --     ∫' x, f x ∂(uniformI R).ℙ = ∫' x in Set.Ioo 0 1, f x := by
-- --   simp [rand_simp,uniformI.measure]; sorry_proof

-- -- theorem uniformI.E (θ : R) (f : Bool → X) :
-- --     (uniformI R).E f = ∫' x in Set.Ioo 0 1, f x := by
-- --   simp only [Rand.E_as_cintegral,uniformI.integral]
