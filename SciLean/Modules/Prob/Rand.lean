import SciLean.Core.Objects.Scalar
import SciLean.Modules.Prob.Init
import SciLean.Modules.Prob.Simps

import Mathlib.MeasureTheory.Measure.GiryMonad


open MeasureTheory ENNReal BigOperators Finset


namespace SciLean.Prob



/-- `x : Rand X` is a random variable of type `X`

You can draw a sample by `x.get : IO X`.
Specification of this random variable is given by the probability measure `x.μ`.

This is Giry monad + its computational realization that can draw random samples.

TODO: Add some kind of specification that `rand` corresponds to `μ`.
      See doc of `Rand.ext` for more discussion. -/
structure Rand (X : Type) [MeasurableSpace X] where
  /-- Probability measure of the random variable
  We use `Erased` because `μ : Measure X` is usually noncomputable but we want keep
  computable `Rand X` -/
  μ : Erased (Measure X)
  is_prob : IsProbabilityMeasure μ.out
  /-- Object that can generate random samples from `X` according to the prob measure `μ` -/
  rand : _root_.Rand X   -- ugh why doesn't mathlib have `Mathlib` namespace?

variable
  {X} [MeasurableSpace X]
  {Y} [MeasurableSpace Y]
  {Z} [MeasurableSpace Z]

instance (x : Rand X) : IsProbabilityMeasure (x.μ.out) := x.is_prob

namespace Rand

/-- Extensionality of random variable.

WARNING: This theorem is inconsistent!!! The random generators `x.rand` and `y.rand` might differ.
         We are not trying to model pseudo-random numbers. We assume that every random number
         generator is a true random number generator. Thus the result of any probabilistic program
         should be independent on the exact generator up to some randomness.

TODO: We might quotient all the random number generators corresponding to the measure `x.μ`  under
      the assumption that they are all true random generators. I believe that such type would be
      a singleton i.e. all the random number generators are all the same.
-/
@[ext]
axiom ext (x y : Rand X) : x.μ = y.μ → x = y


/-- Generate rundom number using IO randomness -/
def get (x : Rand X) : IO X := do
  let stdGen ← ULiftable.up IO.stdGenRef.get
  let (res, new) := x.rand stdGen
  let _ ← ULiftable.up (IO.stdGenRef.set new.down)
  pure res


-- in mathlib this is: MeasurableSpace X → MeasurableSpace (Measure X)
instance : MeasurableSpace (Rand X) := sorry

theorem is_measurable {f : X → Rand Y} (hf : Measurable f) :
    Measurable (fun x => (f x).μ.out) := sorry


----------------------------------------------------------------------------------------------------
-- Probability of an event  ------------------------------------------------------------------2------
----------------------------------------------------------------------------------------------------

noncomputable
def probability (x : Rand X) (s : Set X) : ℝ≥0∞ := x.μ s


----------------------------------------------------------------------------------------------------
-- Monadic structure -------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

def pure (x : X) : Rand X where
  μ := erase (Measure.dirac x)
  is_prob := sorry
  rand := Pure.pure x

def bind (x : Rand X) (f : X → Rand Y) : Rand Y where
  μ := erase (x.μ.out.bind (fun x => (f x).μ))
  is_prob := sorry
  rand := do (f (← x.rand)).rand

def join (x : Rand (Rand X)) : Rand X := x.bind id

-- instance [MeasurableSpace α]: Coe α (Rand α) := ⟨pure⟩


@[rand_simp,simp]
theorem bind_probability (x : Rand X) (f : X → Rand Y) (s : Set Y) (hs : MeasurableSet s)
    (hf : Measurable f) : (bind x f).probability s = ∫⁻ x', (f x').probability s ∂x.μ.out := by

  have := is_measurable hf
  simp (disch:=assumption) [bind, probability, Measure.bind_apply]


theorem measurable_pure' {f : X → Y} (hf : Measurable f) : Measurable fun x => pure (f x) :=
  sorry

theorem measurable_bind' {f : X → Rand Y} (hf : Measurable f) : Measurable fun x => bind x f :=
  sorry


@[rand_simp,simp]
theorem lintegral_bind (x : Rand X) (f : X → Rand Y) (φ : Y → ℝ≥0∞) (hf : Measurable f)
    (hφ : Measurable φ) : ∫⁻ x', φ x' ∂(bind x f).μ = ∫⁻ x', ∫⁻ y', φ y' ∂(f x').μ ∂x.μ := by

  simp [bind]
  apply Measure.lintegral_bind (is_measurable hf) hφ


@[rand_simp,simp]
theorem bind_bind (x : Rand X) (g : X → Rand Y) (f : Y → Rand Z)
    (hg : Measurable g) (hf : Measurable f) : bind (bind x g) f = bind x fun x' => bind (g x') f := by

  ext; simp [bind]
  rw[Measure.bind_bind (m:=x.μ) (is_measurable hg) (is_measurable hf)]


@[rand_simp,simp]
theorem bind_pure (f : X → Rand Y) (hf : Measurable f) (x : X) : bind (pure x) f = f x := by
  ext; simp[bind,pure]
  rw[Measure.bind_dirac (is_measurable hf) x]


----------------------------------------------------------------------------------------------------
-- Notation ----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- we can't use do notation because Rand is not a monad right now (because of the [MeasurableSpace X] argument)
-- this is a small hack to recover it a bit
open Lean.Parser Term in
syntax withPosition("let" funBinder " ~ " term semicolonOrLinebreak ppDedent(ppLine) term) : term
macro_rules
  | `(let $x ~ $y; $b) => do Pure.pure (← `(SciLean.Prob.Rand.bind $y (fun $x => $b))).raw

open Lean Parser
@[app_unexpander Rand.bind] def unexpandRandBind : Lean.PrettyPrinter.Unexpander

| `($(_) $y $f) =>
  match f.raw with
  | `(fun $x:term => $b) => do
    let s ←
      `(let $x ~ $y
        $b)
    Pure.pure s.raw
  | _ => throw ()

| _ => throw ()


----------------------------------------------------------------------------------------------------
-- Arithmetics -------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

instance [Add X] : HAdd X (Rand X) (Rand X) := ⟨fun x' x =>
  let x'' ~ x
  pure (x' + x'')⟩

instance [Add X] : HAdd (Rand X) X (Rand X) := ⟨fun x x' =>
  let x'' ~ x
  pure (x'' + x')⟩

-- instance [Add X] : HAdd (Rand X) (Rand X) (Rand X) := ⟨fun x y =>
--   let x' ~ x
--   let y' ~ y
--   pure (x' + y')⟩

-- todo: add simp theorems that inline these operations


----------------------------------------------------------------------------------------------------
-- Expected Value ----------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section ExpectedValue

variable
  {R} [RealScalar R]
  [NormedAddCommGroup X] [NormedSpace R X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace R X] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace R X] [NormedSpace ℝ Z]


@[rand_simp,simp]
theorem integral_pure (x : X) (φ : X → Y) (hφ : Measurable φ) :
    ∫ x', φ x' ∂(pure x).μ = φ x := sorry


-- todo: I think we need some integrability here
@[rand_simp,simp]
theorem integral_bind (x : Rand X) (f : X → Rand Y) (φ : Y → Z) (hf : Measurable f)
    (hφ : Measurable φ) : ∫ x', φ x' ∂(bind x f).μ = ∫ x', ∫ y', φ y' ∂(f x').μ ∂x.μ := sorry


noncomputable
def E (x : Rand X) (φ : X → Y) : Y := ∫ x', φ x' ∂x.μ

@[rand_simp,simp,rand_push_E]
theorem pure_E (x : X) (φ : X → Y) :
    (pure x).E φ = φ x := by
  simp (disch:=sorry) only [E,rand_simp]

@[simp,rand_push_E]
theorem bind_E (x : Rand X) (f : X → Rand Y) (φ : Y → Z) :
    (x.bind f).E φ = x.E (fun x' => (f x').E φ) := by
  simp (disch:=sorry) only [E,rand_simp]

@[rand_simp,simp,rand_push_E]
theorem zero_E (x : Rand X)  :
    x.E (fun _ => (0 :Y )) = 0 := by
  simp only [E,integral_zero]

@[rand_simp,simp]
theorem add_E (x : Rand X) (φ ψ : X → Y)  :
    x.E (fun x => φ x + ψ x) = x.E φ + x.E ψ := by
  simp only [E]; sorry -- linearity of integral

@[simp]
theorem expectedValue_smul (x : Rand X) (φ : X → ℝ) (y : Y) :
    x.E (fun x' => φ x' • y) = x.E φ • y := by sorry

noncomputable
def mean (x : Rand X) : X := x.E id

@[rand_pull_E]
theorem expectedValue_as_mean (x : Rand X) (φ : X → Y) (hφ : Measurable φ) :
    x.E φ = (x.bind (fun x' => pure (φ x'))).mean := by

  simp (disch:=sorry) [mean,E,hφ]

theorem mean_add  (x : Rand X) (x' : X) : x.mean + x' = (HAdd.hAdd x  x').mean := sorry
theorem mean_add' (x : Rand X) (x' : X) : x' + x.mean = (HAdd.hAdd x' x).mean  := sorry


end ExpectedValue


----------------------------------------------------------------------------------------------------
-- Probability density function --------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

variable (R) [RealScalar R]

/-- Probability density function of `x` w.r.t. the measure `ν`. -/
noncomputable
def pdf (x : Rand X) (ν : Measure X) : X → R :=
  fun x' => Scalar.ofReal R (Measure.rnDeriv x.μ ν x').toReal

noncomputable
abbrev rpdf (x : Rand X) (ν : Measure X) : X → ℝ :=
  fun x' => x.pdf ℝ ν x'

@[rand_simp,simp]
theorem pdf_wrt_self (x : Rand X) : x.pdf R x.μ = 1 := sorry

@[rand_simp,simp]
theorem rpdf_wrt_self (x : Rand X) : x.rpdf x.μ = 1 := by
  funext x; unfold rpdf; rw[pdf_wrt_self]

@[rand_simp,simp]
theorem bind_rpdf (ν : Measure Y) (x : Rand X) (f : X → Rand Y) :
    (x.bind f).rpdf ν = fun y => ∫ x', ((f x').rpdf ν y) ∂x.μ := by
  funext y; simp[Rand.pdf,Rand.bind,Rand.pure]; sorry

@[rand_simp,simp]
theorem bind_pdf (ν : Measure Y) (x : Rand X) (f : X → Rand Y) :
    (x.bind f).pdf R ν = fun y => ∫ x', ((f x').pdf R ν y) ∂x.μ := by
  funext y; simp[Rand.pdf,Rand.bind,Rand.pure]; sorry

open Classical in
@[rand_simp,simp]
theorem pdf_wrt_add (x : Rand X) (μ ν : Measure X) :
    x.pdf R (μ + ν)
    =
    fun x' =>
      if x.μ ⟂ₘ μ then 0 else x.pdf R μ x'
      +
      if x.μ ⟂ₘ ν then 0 else x.pdf R ν x' := sorry


----------------------------------------------------------------------------------------------------
-- Combine -----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

variable {R}
def combine (x y : Rand X) (θ : R) : Rand X := {
  μ := erase ((ENNReal.ofReal (Scalar.toReal R (1-θ))) • x.μ + (ENNReal.ofReal (Scalar.toReal R θ)) • y.μ)
  is_prob := sorry
  rand := fun g => do
    let g : StdGen := g.down
    let N := 1000000000000000
    let (n,g) := _root_.randNat g 0 N
    let θ' := (n : R) / (N : R)
    if θ' ≤ θ then
      y.rand (← ULiftable.up g)
    else
      x.rand (← ULiftable.up g)

}

/-- `x +[θ] y` return random variable `(1-θ)*x + θ*y`.
In other words
- `x` is generated with probability `1-θ`
- `y` is generated with probability `θ` -/
scoped macro x:term:65 " +[" θ:term "] " y:term:64 : term => `(term| combine $x $y $θ)


open Lean Parser
@[app_unexpander Rand.combine] def unexpandRandCombine : Lean.PrettyPrinter.Unexpander
| `($(_) $x $y $θ) => do Pure.pure (← `(term| $x +[$θ] $y)).raw
| _ => throw ()


@[rand_simp,simp]
theorem combine_pdf (x y : Rand X) (μ : Measure X) (θ : R) :
    (x +[θ] y).pdf R μ
    =
    fun x' => (1-θ) * x.pdf R μ x' + θ * y.pdf R μ x' := sorry
