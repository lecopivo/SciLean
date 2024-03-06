import SciLean.Core.Rand.Rand

open MeasureTheory

namespace SciLean

variable
  {R} [RealScalar R]
  {ι} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
  {X} [FinVec ι R X] [Module ℝ X] [MeasureSpace X]

class UniformRand (X : Type _) where
  uniform : Rand X

def uniform (X : Type _) [UniformRand X] : Rand X := UniformRand.uniform

theorem integral_as_uniform_E (R) [RealScalar R] {Y} [AddCommGroup Y] [Module R Y] [Module ℝ Y]
    (f : X → Y) (μ : Measure X) [UniformRand X] :
    ∫' (x : X), f x ∂μ
    =
    (uniform X).E (fun x =>
      let V := Scalar.ofReal R (volume (⊤ : Set X)).toReal
      V⁻¹ • f x) := sorry_proof

-- theorem integral_as_uniform_E' {Y} [AddCommGroup Y] [Module ℝ Y]
--     (f : X → Y) (μ : Measure X) [UniformRand X] :
--     ∫' (x : X), f x ∂μ
--     =
--     (uniform X).E (fun x =>
--       let density := (μ.rnDeriv (uniform X).ℙ x)
--       density.toReal • f x) := sorry_proof
