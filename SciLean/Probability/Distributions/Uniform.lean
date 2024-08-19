import Mathlib.MeasureTheory.Constructions.Prod.Basic

import SciLean.Analysis.AdjointSpace.Geometry
import SciLean.Data.ArrayType.Algebra
import SciLean.Data.DataArray
import SciLean.Probability.Rand

open MeasureTheory Set

namespace SciLean.Rand

set_option deprecated.oldSectionVars true
variable {R} [RealScalar R] [MeasureSpace R]

/-- Class providing uniform sampler from the set `A`. -/
class UniformRand {X : Type _} (A : Set X) [MeasureSpace X] where
  uniform : Rand X
  is_uniform : ∀ x, uniform.ℙ.rnDeriv volume x = 1 / volume A
  is_prob : LawfulRand uniform

export UniformRand (uniform)


@[simp,  simp_core]
theorem uniform.pdf [MeasureSpace X] (A : Set X) [UniformRand A] :
    (uniform A).pdf R volume
    =
    fun _ => (Scalar.ofENNReal (R:=R) (volume A))⁻¹ := by
  unfold Rand.pdf uniform
  simp [UniformRand.is_uniform]
  sorry_proof



----------------------------------------------------------------------------------------------------
-- Integral ----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

theorem integral_eq_E (R) [RealScalar R]
    {X} [MeasureSpace X]
    {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedSpace R Y]
    (r : Rand X) (f : X → Y) (μ : Measure X) /- (hrμ : r.ℙ ≪ μ) -/ :
    ∫ x, f x ∂μ
    =
    r.𝔼 (fun x =>
      let pdf := r.pdf R μ x
      pdf • f x) := sorry_proof

theorem integral_eq_uniform_E (R) [RealScalar R]
    {X} [MeasureSpace X]
    {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedSpace R Y]
    (f : X → Y) (A : Set X) [UniformRand A] :
    ∫ x in A, f x
    =
    (uniform A).𝔼 (fun x =>
      let V : R := Scalar.ofENNReal (volume A)
      V • f x) := sorry_proof

theorem weakIntegral_as_uniform_E_in_set (R) [RealScalar R]
    {X} [MeasureSpace X]
    {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedSpace R Y]
    (f : X → Y) (A : Set X) [UniformRand A] :
    weakIntegral volume f
    =
    (uniform A).𝔼 (fun x =>
      let V : R := Scalar.ofENNReal (volume A)
      V • f x) := sorry_proof


----------------------------------------------------------------------------------------------------
-- Constructions -----------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

instance {α} [MeasureSpace α] {β} [MeasureSpace β]
    (A : Set α) [UniformRand A] (B : Set β) [UniformRand B] :
    UniformRand (A.prod B) where
  uniform := do
    let a ← uniform A
    let b ← uniform B
    return (a,b)
  is_uniform := by sorry_proof
  is_prob := by sorry_proof


instance {α} [MeasureSpace α] {β} [MeasureSpace β]
    (A : Set α) [UniformRand A] (B : Set β) [UniformRand B] :
    UniformRand (A ×ˢ B) := by simp[SProd.sprod]; infer_instance



----------------------------------------------------------------------------------------------------
-- Intervals ---------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- WARNING: These instances are breaking consistency!!!
--          ugh how to deal with empty intervals ?!
--          Do we support only Iuu



instance (a b : R) : UniformRand (Icc a b) where
  uniform := do
    let x ← uniformI R
    return a + x * (b - a)
  is_uniform := by sorry_proof
  is_prob := by sorry_proof

instance (a b : R) : UniformRand (Ioo a b) where
  uniform := do
    let x ← uniformI R
    return a + x * (b - a)
  is_uniform := by sorry_proof
  is_prob := by sorry_proof

instance (a b : R) : UniformRand (Ioc a b) where
  uniform := do
    let x ← uniformI R
    return a + x * (b - a)
  is_uniform := by sorry_proof
  is_prob := by sorry_proof

instance (a b : R) : UniformRand (Set.Ico a b) where
  uniform := do
    let x ← uniformI R
    return a + x * (b - a)
  is_uniform := by sorry_proof
  is_prob := by sorry_proof

set_option linter.unusedVariables false in
@[simp,  simp_core]
theorem Set.Ioo_volume (a b : R) (h : a ≤ b) :
  (volume (Set.Ioo a b)) = Scalar.toENNReal (b - a) := sorry_proof

set_option linter.unusedVariables false in
@[simp,  simp_core]
theorem Set.Ioc_volume (a b : R) (h : a ≤ b) :
  (volume (Set.Ioc a b)) = Scalar.toENNReal (b - a) := sorry_proof

set_option linter.unusedVariables false in
@[simp,  simp_core]
theorem Set.Ico_volume (a b : R) (h : a ≤ b) :
  (volume (Set.Ico a b)) = Scalar.toENNReal (b - a) := sorry_proof

set_option linter.unusedVariables false in
@[simp,  simp_core]
theorem Set.Icc_volume (a b : R) (h : a ≤ b) :
  (volume (Set.Icc a b)) = Scalar.toENNReal (b - a) := sorry_proof



----------------------------------------------------------------------------------------------------
-- Ball --------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


variable (R)
/-- Helper class allowing us to draw samples from a ball over a generic type `X`.

There are many variants of the space `ℝⁿ` like `ℝ×ℝ`, `ℝ^[n]`, `ℝ^[n]×ℝ^[n]`, etc. with the help
of this class we can effectivelly define sampling frmo a ball inductively. -/
class RejectionSampleBall₂ (X : Type) [NormedAddCommGroup X] [AdjointSpace R X]  where
  sample : Rand X
variable {R}


instance : RejectionSampleBall₂ (R:=R) R where
  sample := do
    let x ← uniformI R
    return 2*x-1

instance
  {X} [NormedAddCommGroup X] [AdjointSpace R X] [RejectionSampleBall₂ (R:=R) X]
  {Y} [NormedAddCommGroup Y] [AdjointSpace R Y] [RejectionSampleBall₂ (R:=R) Y] :
  RejectionSampleBall₂ (R:=R) (X×Y) where

  sample := do
    let go : Rand (Option (X×Y)) := do
      let x ← RejectionSampleBall₂.sample (R:=R) (X:=X)
      let xnorm2 := ‖x‖₂²[R]
      if xnorm2 > 1 then return none
      let y ← RejectionSampleBall₂.sample (R:=R) (X:=Y)
      let ynorm2 := ‖y‖₂²[R]
      if xnorm2 + ynorm2 > 1 then return none
      return (x,y)

    while true do
      if let .some x ← go then
        return x
      else
        continue

    return 0

instance
  {I : Type} [IndexType I]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace R X] [RejectionSampleBall₂ (R:=R) X] [PlainDataType X] :
  RejectionSampleBall₂ (R:=R) (X^[I]) where

  sample := do
    let go : Rand (Option (X^[I])) := do

      let mut s : R := 0
      let mut x : X^[I] := 0
      for i in fullRange I do
        let xi ← RejectionSampleBall₂.sample (R:=R) (X:=X)
        s := s + ‖xi‖₂²[R]
        if s > 1 then return none
        x[i] := xi

      return x

    while true do
      if let .some x ← go then
        return x
      else
        continue

    return 0


instance {X} [NormedAddCommGroup X] [AdjointSpace R X] [RejectionSampleBall₂ (R:=R) X] [MeasureSpace X]
    (x : X) (r : R) :
    UniformRand (closedBall₂ x r) where
  uniform := do
    let y ← RejectionSampleBall₂.sample (R:=R) (X:=X)
    return r • y + x
  is_uniform := sorry_proof
  is_prob := sorry_proof
