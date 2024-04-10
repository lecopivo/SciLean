import SciLean.Core.Rand.Rand

open MeasureTheory

namespace SciLean.Rand

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
    (uniform X).𝔼 (fun x =>
      let V : R := Scalar.ofENNReal (volume (Set.univ : Set X))
      V • f x) := sorry_proof


theorem integral_as_uniform_E_in_set (R) [RealScalar R] {Y} [AddCommGroup Y] [SMul R Y] [Module ℝ Y]
    (f : X → Y) (A : Set X) [UniformRand A] :
    ∫' x in A, f x
    =
    (uniform A).𝔼 (fun x =>
      let V : R := Scalar.ofENNReal (volume (Set.univ : Set X))
      V • f x) := sorry_proof

-- theorem integral_as_uniform_E' {Y} [AddCommGroup Y] [Module ℝ Y]
--     (f : X → Y) (μ : Measure X) [UniformRand X] :
--     ∫' (x : X), f x ∂μ
--     =
--     (uniform X).E (fun x =>
--       let density := (μ.rnDeriv (uniform X).ℙ x)
--       density.toReal • f x) := sorry_proof
