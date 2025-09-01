import SciLean.Probability.Rand
import SciLean.Probability.Tactic
import SciLean.Analysis.SpecialFunctions.Gaussian

open MeasureTheory ENNReal Finset

namespace SciLean.Rand

variable
  {R} [RealScalar R] [MeasureSpace R]
  {U} [NormedAddCommGroup U] [AdjointSpace R U] [MeasureSpace U]

set_default_scalar R


----------------------------------------------------------------------------------------------------
-- Generating functions ----------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

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


----------------------------------------------------------------------------------------------------

/-- Normal random variable with mean `μ` and standard deviation `σ`. -/
def normal (μ σ : R)  : Rand R := {
  spec := default -- erase (fun φ => ∫ x, φ x * (Scalar.toReal R (gaussian μ σ x)))
  rand := do
    let x ← (generateNormalV2 R).rand
    return σ * x + μ
}

instance (μ σ : R) : LawfulRand (normal μ σ) where
  is_measure := sorry_proof
  is_prob    := sorry_proof

@[simp, simp_core]
theorem normal.pdf (μ σ : R) :
    (normal μ σ).pdf R volume
    =
    gaussian μ σ := sorry_proof


@[simp, simp_core]
theorem normal.map_add_right (μ σ : R) (θ : R) :
    (normal μ σ).map (fun x => x + θ)
    =
    (normal (μ+θ) σ) := sorry_proof

@[simp, simp_core]
theorem normal.map_add_left (μ σ : R) (θ : R) :
    (normal μ σ).map (fun x => θ + x)
    =
    (normal (θ + μ) σ) := sorry_proof

@[simp, simp_core]
theorem normal.map_sub_right (μ σ : R) (θ : R) :
    (normal μ σ).map (fun x => x - θ)
    =
    (normal (μ-θ) σ) := sorry_proof

theorem normal_reparameterize (μ σ : R) :
    normal μ σ = (normal 0 1).map (fun x => σ • x + μ) := sorry_proof


-- ----------------------------------------------------------------------------------------------------
-- -- Derivatives -------------------------------------------------------------------------------------
-- ----------------------------------------------------------------------------------------------------

-- variable
--   {W} [Vec R W]
--   {Y} [Vec R Y]
--   {Z} [Vec R Z] [Module ℝ Z]

-- noncomputable
-- def normalFDμ (μ dμ : U) (σ : R) : 𝒟'(U,R×R) :=
--   fun φ ⊸ (∫' x, φ x * gaussian μ σ x, ∫' x, φ x * (∂ μ':=μ;dμ, gaussian μ' σ x))

-- @[fun_trans]
-- theorem normal.arg_μ.parDistribFwdDeriv (μ : W → R) (σ : R)
--   (hμ : CDifferentiable R μ) :
--   parDistribFwdDeriv (fun w => (normal (μ w) σ).ℙ.toDistribution (R:=R))
--   =
--   fun w dw =>
--     let μdμ := fwdDeriv R μ w dw
--     normalFDμ μdμ.1 μdμ.2 σ := sorry_proof

-- theorem normalFDμ_score (μ dμ : R) (σ : R) (f : R → Y) (L : (R×R) ⊸ Y ⊸ Z) :
--     (normalFDμ μ dμ σ).extAction f L
--     =
--     (normal μ σ).𝔼 (fun x => L (1, - (1/(σ^2)) * ⟪x-μ,-dμ⟫) (f x)) := sorry_proof
