import Mathlib.MeasureTheory.Measure.VectorMeasure
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Basic

import SciLean.Modules.Prob.Rand
import SciLean.Modules.Prob.TestFunctionExtension


open MeasureTheory ENNReal BigOperators Finset

namespace SciLean.Prob

/-- Tangent space of `Rand X`. It is the space of distributions `𝒟' X` which is not yet defined
in mathlib.

When differentiating function `f : X → Rand Y` we can understand it as a function to the space of
signed measures, `f : X → SignedMeasure Y`, becase `Rand Y` is just an affine subspace of `SignedMeasure Y`.
Taking derivative of `f` yields `fderiv ℝ f : X → X →L[ℝ] SignedMeasure Y`. To be more precise
we need to take the space of all finite signed measures with finite total variation. Such space form
a Banach space and `fderiv ℝ f` is well defined.

Unfortunately, the functio `fun x => Measure.dirac x` is not differentiable in this manner as the
result is not a signed measure. Thus we need to embedd `Rand Y` into the space of distributions `𝒟' Y`.
This space is locally convex topological space and differentiating `f : X → 𝒟' Y` can have meaning again.
Unfortunately, mathlib does not have the definition of such derivative right now.
   -/
structure DRand (X : Type) [MeasurableSpace X] where
  action : (X → ℝ) → ℝ


-- This instance should be fine because `DRand X` just the space of
-- distributions `𝒟' X` which is a topological space thus a Borel space.
instance {X} [MeasurableSpace X] : MeasurableSpace (DRand X) := sorry

noncomputable
def randDeriv {X} [NormedAddCommGroup X] [NormedSpace ℝ X] {Y} [MeasurableSpace Y]
    (f : X → Rand Y) (x dx : X) : DRand Y := {
  -- differentiate `f` as a functin from `X` to the space of finite measures
  -- with finite total variation and then split it to positive and negative part
  action := fun φ => fderiv ℝ (fun x' => ∫ y, φ y ∂(f x').μ) x dx
}


variable
  {R} [RealScalar R]
  {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace R X] [MeasurableSpace X]
  {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedSpace R X] [MeasurableSpace Y]
  {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedSpace R X] [MeasurableSpace Z]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace R X] [MeasurableSpace W]

namespace DRand
open Rand


-- todo: some smoothenss
theorem ext (x y : DRand X) : (∀ φ, x.action φ = y.action φ) → x = y := sorry

def dirac (x : X) : DRand X := {
  action := fun φ => φ x
}

----------------------------------------------------------------------------------------------------
-- Semi monadic operations -------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
noncomputable

def _root_.SciLean.Prob.Rand.dpure (x dx : X) : DRand X := {
  action := fun f => fderiv ℝ f x dx
}
noncomputable

def bindDR (x : DRand X) (f : X → Rand Y) : DRand Y := {
  action := fun φ => x.action (fun x' => (f x').E φ)
}
noncomputable

def _root_.SciLean.Prob.Rand.bindRD (x : Rand X) (f : X → DRand Y) : DRand Y := {
  action := fun φ => x.E (fun x' => (f x').action φ)
}
noncomputable

def _root_.SciLean.Prob.Rand.joinRD (x : Rand (DRand X)) : DRand X := x.bindRD id
noncomputable

def joinDR (x : (DRand (Rand X))) : DRand X := x.bindDR id

@[rand_simp]
theorem dpure_action (x dx : X) : (Rand.dpure x dx).action φ = fderiv ℝ φ x dx := by
  simp[Rand.dpure]



----------------------------------------------------------------------------------------------------
-- Expected value change ---------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

noncomputable
def dE (x : DRand X) (φ : X → Y) : Y :=
  testFunctionExtension x.action φ

noncomputable
def dmean (x : DRand X) : X := x.dE id

@[rand_simp,simp]
theorem dpure_dE (x dx : X) (φ : X → Y) :
    (dpure x dx).dE φ = fderiv ℝ φ x dx := by

  simp only [bindRD,dE,dpure,rand_simp]

  apply testFunctionExtension_ext
  intro φ y; dsimp;
  simp (disch:=sorry) [fderiv_smul]


@[rand_simp,simp]
theorem bindRD_dE (x : Rand X) (f : X → DRand Y) (φ : Y → Z) :
    (x.bindRD f).dE φ = x.E (fun x' => (f x').dE φ) := by

  simp only [bindRD,dE,rand_simp,E]

  apply testFunctionExtension_ext
  intro φ y
  simp only [testFunctionExtension_test_function]
  sorry -- just linearity of integral


@[rand_simp,simp]
theorem bindDR_dE (x : DRand X) (f : X → Rand Y) (φ : Y → Z) :
    (x.bindDR f).dE φ = x.dE (fun x' => (f x').E φ) := by

  simp only [bindDR,dE,rand_simp, E]

  apply testFunctionExtension_ext
  intro φ y; symm; dsimp
  -- linearity of integral before applying this
  -- simp only [testFunctionExtension_test_function]
  sorry


----------------------------------------------------------------------------------------------------
-- Monadic rules - one work only under computing expected value change -----------------------------
----------------------------------------------------------------------------------------------------

@[rand_simp, simp]
theorem bindDR_pure (x : DRand X) (f : X → Y) (φ : Y → Z) :
    (x.bindDR (fun x' => pure (f x'))).dE φ
    =
    x.dE (fun x' => φ (f x')) := by

  simp only [bindDR,dE,rand_simp]
  apply testFunctionExtension_ext
  intro φ y; symm; dsimp
  rw[testFunctionExtension_test_function]


@[rand_simp, simp]
theorem pure_bindRD (x : X) (f : X → DRand Y) :
    (Rand.pure x).bindRD f = f x := by

  simp only [bindRD,dE,rand_simp]


-- This is the only unusual monadic rule
@[rand_simp, simp]
theorem bindRD_dpure (x : Rand X) (f df : X → Y) (φ : Y → Z) :
    (x.bindRD (fun x' => dpure (f x') (df x'))).dE φ
    =
    x.E (fun x' => fderiv ℝ φ (f x') (df x')) := by

  simp only [rand_simp]


@[rand_simp, simp]
theorem dpure_bindDR (x dx : X) (f : X → Rand Y) :
    ((dpure x dx).bindDR f) = randDeriv f x dx := by

  apply ext; intro φ

  simp only [bindDR, dpure, dE, randDeriv,E]


@[rand_simp, simp]
theorem bindDR_bindDR (x : DRand X) (g : X → Rand Y) (f : Y → Rand Z) :
    (x.bindDR g).bindDR f = (x.bindDR (fun x' => (g x').bind f)) := by

  simp (disch:=sorry) only [bindDR,rand_simp,rand_push_E]


@[rand_simp, simp]
theorem bindRD_bindDR (x : Rand X) (g : X → DRand Y) (f : Y → Rand Z) :
    (x.bindRD g).bindDR f = x.bindRD (fun x' => (g x').bindDR f) := by

  simp (disch:=sorry) only [bindDR,bindRD,rand_simp]



----------------------------------------------------------------------------------------------------
-- Arithmetic operations ---------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

instance : Zero (DRand X) := ⟨{
  action := fun _ => 0
}⟩

instance : Add (DRand X) := ⟨fun x y => {
  action := fun φ => x.action φ + y.action φ
}⟩

instance : Sub (DRand X) := ⟨fun x y => {
  action := fun φ => x.action φ - y.action φ
}⟩

noncomputable
instance : SMul ℝ (DRand X) := ⟨fun s x => {
  action := fun φ => s • (x.action φ)
}⟩

noncomputable
instance : SMul R (DRand X) := ⟨fun s x => {
  action := fun φ => (Scalar.toReal R s) • (x.action φ)
}⟩


@[rand_simp]
theorem action_zero : (0 : DRand X).action φ = 0 := rfl

-- todo: add some smoothenss assumption on `φ`
@[rand_simp]
theorem action_add (x y : DRand X) (φ : X → ℝ) : (x + y).action φ = x.action φ + y.action φ := rfl

@[rand_simp]
theorem action_smul (s : R) (x : DRand X) (φ : X → ℝ) : (s • x).action φ = (Scalar.toReal R s) • x.action φ := rfl

-- this is unnecessary - we should add simp theorem `Scalar.toReal ℝ s = s` for `x : ℝ` and remove this
@[rand_simp]
theorem action_smul_real (s : ℝ) (x : DRand X) (φ : X → ℝ) : (s • x).action φ = s • x.action φ := rfl

@[rand_simp]
theorem smul_one_drand (x : DRand X) : (1:R) • x = x := sorry

@[rand_simp]
theorem add_dE (x y : DRand X) (φ : X → Y) :
    (x + y).dE φ
    =
    x.dE φ + y.dE φ := sorry


----------------------------------------------------------------------------------------------------
-- Measure -----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

/-- `x` can be expressed as a signed measure -/
def IsMeasure (x : DRand X) : Prop :=
  ∃ μ : SignedMeasure X, False
    -- ∀ (φ : X → ℝ), x.action φ = ∫ x', φ x' ∂μ

open Classical in
/-- If `x` can be expressed as a measure return it otherwise return zero. -/
noncomputable
def measure (x : DRand X) : SignedMeasure X :=
  if h : x.IsMeasure then
    choose h
  else
    0

----------------------------------------------------------------------------------------------------
-- Density function w.r.t to a random variable -----------------------------------------------------
----------------------------------------------------------------------------------------------------


variable (R)
noncomputable
def density (x : DRand X) (μ : Measure X) : X → R :=
  fun x' => Scalar.ofReal R (x.measure.rnDeriv μ x')
variable {R}

noncomputable
abbrev rdensity (x : DRand X) (μ : Measure X) : X → ℝ :=
  fun x' => (x.density ℝ μ x')

@[simp,rand_simp]
theorem rdensity_of_zero (μ : Measure X):
    (0 : DRand X).rdensity μ = 0 := sorry

@[simp,rand_simp]
theorem density_of_zero (μ : Measure X):
    (0 : DRand X).density R μ = 0 := sorry

@[simp,rand_simp]
theorem density_of_add (x y : DRand X) (μ : Measure X):
    (x + y).density R μ = x.density R μ + y.density R μ := sorry

@[simp,rand_simp]
theorem density_of_sub (x y : DRand X) (μ : Measure X):
    (x - y).density R μ = x.density R μ - y.density R μ := sorry

@[simp,rand_simp]
theorem density_smul (x : DRand X) (s : R) (μ : Measure X) :
    (s • x).density R μ = fun x' => s • x.density R μ x' := sorry

@[simp,rand_simp]
theorem rdensity_smul (x : DRand X) (s : ℝ) (μ : Measure X) :
    (s • x).rdensity μ = fun x' => s • x.rdensity μ x' := sorry
