import SciLean.Core.Rand.Rand
import SciLean.Core.Integral.RnDeriv

open MeasureTheory

namespace SciLean.Rand

variable
  {R} [RealScalar R] [MeasureSpace R]
  {ι} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
  {X} [FinVec ι R X] [Module ℝ X] [MeasureSpace X]

class UniformRand (X : Type _) where
  uniform : Rand X

def uniform (X : Type _) [UniformRand X] : Rand X := UniformRand.uniform

theorem cintegral_as_uniform_E (R) [RealScalar R] {Y} [AddCommGroup Y] [Module R Y] [Module ℝ Y]
    (f : X → Y) (μ : Measure X) [UniformRand X] :
    ∫' (x : X), f x ∂μ
    =
    (uniform X).𝔼 (fun x =>
      let V : R := Scalar.ofENNReal (volume (Set.univ : Set X))
      V • f x) := sorry_proof


theorem cintegral_as_uniform_E_in_set (R) [RealScalar R] {Y} [AddCommGroup Y] [SMul R Y] [Module ℝ Y]
    (f : X → Y) (A : Set X) [UniformRand A] :
    ∫' x in A, f x
    =
    (uniform A).𝔼 (fun x =>
      let V : R := Scalar.ofENNReal (volume A)
      V • f x) := sorry_proof



class UniformRand' {X : Type _} (A : Set X) [MeasureSpace X] where
  uniform : Rand X
  is_uniform : ∀ x, uniform.ℙ.rnDeriv volume x = 1 / volume A

def uniform' {X : Type _} (A : Set X) [MeasureSpace X] [UniformRand' A] : Rand X := UniformRand'.uniform A

theorem integral_as_uniform_E_in_set (R) [RealScalar R]
    {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedSpace R Y]
    (f : X → Y) (A : Set X) [UniformRand' A] :
    ∫ x in A, f x
    =
    (uniform' A).𝔼 (fun x =>
      let V : R := Scalar.ofENNReal (volume A)
      V • f x) := sorry_proof


open Set

instance (a b : R) : UniformRand' (Icc a b) where
  uniform := do
    let x ← uniformI R
    return a + x * (b - a)
  is_uniform := by
    sorry_proof


instance (a b : R) : UniformRand' (Ioo a b) where
  uniform := do
    let x ← uniformI R
    return a + x * (b - a)
  is_uniform := by
    sorry_proof


instance {α} [MeasureSpace α] {β} [MeasureSpace β]
    (A : Set α) [UniformRand' A] (B : Set β) [UniformRand' B] :
    UniformRand' (A.prod B) where
  uniform := do
    let a ← uniform' A
    let b ← uniform' B
    return (a,b)
  is_uniform := by
    sorry_proof


instance {α} [MeasureSpace α] {β} [MeasureSpace β]
    (A : Set α) [UniformRand' A] (B : Set β) [UniformRand' B] :
    UniformRand' (A ×ˢ B) := by simp[SProd.sprod]; infer_instance
