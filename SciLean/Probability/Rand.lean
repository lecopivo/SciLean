module

public import Mathlib.Data.Erased
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad

public import SciLean.Algebra.IsAffineMap
public import SciLean.Analysis.Scalar
public import SciLean.Logic.Function.Bijective
public import SciLean.MeasureTheory.WeakIntegral
public import SciLean.Meta.Notation.Do
public import SciLean.Meta.SimpAttr
public import SciLean.Probability.SimpAttr
public import SciLean.Util.Limit

@[expose] public section
set_option linter.overlappingInstances false


-- import Mathlib.Control.Random
-- import SciLean.Mathlib.MeasureTheory.WeakIntegral
-- import SciLean.Core.FunctionPropositions.IsAffineMap
-- import SciLean.Core.Objects.Scalar
-- import SciLean.Core.Notation



open MeasureTheory ENNReal BigOperators Finset

namespace SciLean

abbrev erase (a : α) : Erased α := .mk a

@[simp,simp_core]
theorem erase_out {α} (a : α) : (erase a).out = a := by simp[erase]


/-- `x : Rand X` is a random variable of type `X`

You can:
  - generate sample with `x.get : IO X`
  - get probability measure with `x.ℙ : Measure X`

The internal fields `spec` and `rand` are just an internal implementation of `Rand` and should not
be accessed by normal users.

TODO: Hide implementation using quotients or something like that
-/
structure Rand (X : Type _)  where
  /-- `spec` defines a probability measure by computing an expectation. This means if `x : Rand X`
  corresponds to a probability measure `μ` then for `φ : X → ℝ`
  ```
  x.spec.out φ = ∫ x, φ x ∂μ
  ```

  Using `(X→ℝ)→ℝ` instead of `Measure X` for the specification of random variables has the
  advantage that we can reuse Lean's `do` notation.
  -/
  spec : Erased ((X→ℝ)→ℝ)
  /-- `rand` is a pseudo randon number generator implemented using the "Standard" number generator
  -/
  rand : StateM StdGen X


namespace Rand

def _root_.Function.IsMeasure {X} [MeasurableSpace X] (F : (X → ℝ) → ℝ) : Prop :=
  ∃ μ : Measure X, ∀ (f : X → ℝ), F f = ∫ x, f x ∂μ

open Classical in

/-- Probability measure of a random variable -/
noncomputable
def ℙ {X} [MeasurableSpace X] (r : Rand X) : Measure X :=
  if h : r.spec.out.IsMeasure then
    choose h
  else
    0

/-- Specification of `x : Rand X` is really saying that it is a probability measure. -/
class LawfulRand (x : Rand X) [MeasurableSpace X] : Prop where
  is_measure : x.spec.out.IsMeasure
  is_prob : IsProbabilityMeasure x.ℙ

set_option deprecated.oldSectionVars true

variable {X Y Z : Type _}
  [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace Y] [MeasurableSingletonClass Y]

instance instIsProbabilityMeasureℙ (x : Rand X) [inst : LawfulRand x] : IsProbabilityMeasure (x.ℙ) := inst.is_prob


/-- Extensionality of random variable.

WARNING: This theorem is inconsistent!!! The random generators `x.rand` and `y.rand` might differ.
         We are not trying to model pseudo-random numbers. We assume that every random number
         generator is a true random number generator. Thus the result of any probabilistic program
         should be independent on the exact generator up to some randomness.

TODO: We might quotient all the random number generators corresponding to the measure `x.ℙ`  under
      the assumption that they are all true random generators. I believe that such type would be
      a singleton i.e. all the random number generators are all the same.
-/
@[ext]
axiom ext (x y : Rand X) : x.spec.out = y.spec.out → x = y


/-- Generate rundom number using IO randomness -/
def get (x : Rand X) : IO X := do
  let stdGen ← IO.stdGenRef.get
  let (res, new) := x.rand stdGen
  let _ ← IO.stdGenRef.set new
  pure res


----------------------------------------------------------------------------------------------------
-- Monadic structure -------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

instance : Monad Rand where
  pure x := {
    spec := erase (fun φ => φ x),
    rand := pure x
  }
  bind x f := {
    spec := default, -- erase (fun φ => x.spec.out (fun x => (f x).spec.out φ)),
    rand := bind x.rand (fun x => (f x).rand)
  }


instance : LawfulMonad Rand where
  bind_pure_comp := by intros; rfl
  bind_map       := by intros; rfl
  pure_bind      := sorry_proof -- by intros; ext; simp[Bind.bind,Pure.pure]
  bind_assoc     := by intros; ext; simp[Bind.bind]
  map_const      := by intros; ext; rfl
  id_map         := sorry_proof -- by intros; ext; simp[Bind.bind,Pure.pure,id,Functor.map]
  seqLeft_eq     := by intros; ext; simp[Bind.bind,Pure.pure,Seq.seq,Functor.map,SeqLeft.seqLeft]
  seqRight_eq    := by intros; ext; simp[Bind.bind,Pure.pure,Seq.seq,Function.const,Functor.map,SeqRight.seqRight]
  pure_seq       := by intros; ext; simp[Bind.bind,Pure.pure,Seq.seq,Functor.map]


-- this needs some integrability and lawfulness of Rand
theorem swap_bind (f : X → Y → Z) (x : Rand X) (y : Rand Y) :
    (do let x' ← x; let y' ← y; pure (f x' y'))
    =
    (do let y' ← y; let x' ← x; pure (f x' y')) := by
  ext x_1 : 2
  rfl


@[simp, simp_core]
theorem pure_ℙ (x : X) : (pure x : Rand X).ℙ = Measure.dirac x := by
  have hspec : (pure x : Rand X).spec.out = fun φ : X → ℝ => φ x := by
    simp [Pure.pure]
  have hm : ((pure x : Rand X).spec.out).IsMeasure := by
    refine ⟨Measure.dirac x, ?_⟩
    intro f
    rw [hspec]
    simp [integral_dirac]
  rw [Rand.ℙ]
  split
  case isFalse h => exact absurd hm h
  case isTrue h =>
    -- `ℙ` picks *some* measure with the given integrals, we show it has to be `dirac x`
    set μ := Classical.choose h with hμdef
    have hμ : ∀ f : X → ℝ, (pure x : Rand X).spec.out f = ∫ y, f y ∂μ :=
      Classical.choose_spec h
    have h1 : (1:ℝ) = ∫ _y, (1:ℝ) ∂μ := by
      have := hμ (fun _ => (1:ℝ)); rw [hspec] at this; simpa using this
    have hfin : IsFiniteMeasure μ := by
      by_contra hc
      have hnint : ¬ Integrable (fun _ : X => (1:ℝ)) μ := by
        intro hint
        rcases integrable_const_iff.mp hint with h0 | hfin'
        · exact one_ne_zero h0
        · exact hc hfin'
      rw [integral_undef hnint] at h1
      exact one_ne_zero h1
    ext A hA
    have hind := hμ (A.indicator (fun _ => (1:ℝ)))
    rw [hspec, integral_indicator_const _ hA] at hind
    simp only [smul_eq_mul, mul_one] at hind
    rw [Measure.dirac_apply' _ hA]
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx] at hind
      simp only [Set.indicator_of_mem hx, Pi.one_apply]
      exact (ENNReal.toReal_eq_one_iff _).mp hind.symm
    · rw [Set.indicator_of_notMem hx] at hind
      simp only [Set.indicator_of_notMem hx]
      exact ((ENNReal.toReal_eq_zero_iff _).mp hind.symm).resolve_right (measure_ne_top μ A)


----------------------------------------------------------------------------------------------------
-- Arithmetics -------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

instance [Add X] : HAdd X (Rand X) (Rand X) := ⟨fun x' x => do
  let x'' ← x
  pure (x' + x'')⟩

instance [Add X] : HAdd (Rand X) X (Rand X) := ⟨fun x x' => do
  let x'' ← x
  pure (x'' + x')⟩

-- instance [Add X] : HAdd (Rand X) (Rand X) (Rand X) := ⟨fun x y =>
--   let x' ~ x
--   let y' ~ y
--   pure (x' + y')⟩

-- todo: add simp theorems that inline these operations

----------------------------------------------------------------------------------------------------
-- Simple Random Variable functions ----------------------------------------------------------------
----------------------------------------------------------------------------------------------------

abbrev map (r : Rand X) (f : X → Y) : Rand Y := do
  let x' ← r
  return f x'

/-- Marginal distribution for the first component of a pair. -/
abbrev fst (r : Rand (X×Y)) : Rand X := do
  let (x,_) ← r
  return x

/-- Marginal distribution for the second component of a pair. -/
abbrev snd (r : Rand (X×Y)) : Rand Y := do
  let (_,y) ← r
  return y


@[simp, simp_core]
theorem map_ℙ  (r : Rand X) (f : X → Y) :
  (r.map f).ℙ = r.ℙ.map f := sorry_proof

@[simp, simp_core]
theorem map_ℙ'  (r : Rand X) (f : X → Y) :
  (f <$> r).ℙ = r.ℙ.map f := map_ℙ r f


----------------------------------------------------------------------------------------------------
-- Expected Value ----------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section ExpectedValue

variable
  {R} [RealScalar R]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y] [LocallyConvexSpace ℝ Y]
  [AddCommGroup Z] [Module ℝ Z] [TopologicalSpace Z] [LocallyConvexSpace ℝ Z]
  {U} [AddCommGroup U] [Module ℝ U] [TopologicalSpace U] [LocallyConvexSpace ℝ U]
  -- {U} [AddCommGroup U] [TopologicalSpace U] [TopologicalAddGroup U] [Module ℝ U] [LocallyConvexSpace ℝ U]

noncomputable
def E (r : Rand X) (φ : X → Y) : Y := weakIntegral r.ℙ  φ

@[simp, simp_core, rand_push_E]
theorem pure_𝔼 (x : X) (φ : X → Y) :
    (pure (f:=Rand) x).E φ = φ x := by simp [E]

-- What are the right assumptions here? Lambda lawfulness of `x` and `f x'` and integrability of `φ`
@[rand_push_E]
theorem bind_E (r : Rand X) (f : X → Rand Y) (φ : Y → Z) :
    (r >>= f).E φ = r.E (fun x' => (f x').E φ) := by simp[E]; sorry_proof

-- todo: We might want this to hold without lawfulness
-- consider adding as a property inside of `Distribution` or `Rand`
@[simp, simp_core, rand_push_E]
theorem E_zero (r : Rand X) :
    r.E (fun _ => (0 : Y)) = 0 := by simp[E]

@[simp, simp_core, add_pull, rand_push_E]
theorem E_add (r : Rand X) (φ ψ : X → U)
    (hφ : WeakIntegrable φ r.ℙ) (hψ : WeakIntegrable ψ r.ℙ) :
    r.E (fun x => φ x + ψ x) = r.E φ + r.E ψ := by
  simp[E]; rw[weakIntegral_add] <;> assumption

@[simp, simp_core, smul_pull, rand_push_E]
theorem E_smul (r : Rand X) (φ : X → ℝ) (y : Y) :
    r.E (fun x' => φ x' • y) = r.E φ • y := by sorry_proof

@[simp, simp_core, rand_push_E]
theorem map_E (f : X → Y) {r : Rand X} {φ : Y → Z} :
    (f <$> r).E φ
    =
    r.E (φ ∘ f) := by
  simp[E]
  rw[weakIntegral_map sorry_proof sorry_proof]
  rfl

theorem reparameterize [Nonempty X] (f : X → Y) (hf : f.Injective) {r : Rand X} {φ : X → Z} :
    r.E φ
    =
    let invf := f.invFun
    (r.map f).E (fun y => φ (invf y)) := by
  show _ = (f <$> r).E _
  rw [map_E]
  simp [Function.comp_def, Function.leftInverse_invFun hf _]

section Mean

variable [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [LocallyConvexSpace ℝ X]

noncomputable
def mean (r : Rand X) : X := r.E id

@[rand_pull_E]
theorem expectedValue_as_mean (x : Rand X) (φ : X → Y) :
    x.E φ = (x.map φ).mean := by
  show _ = (φ <$> x).E id
  rw [map_E]
  rfl

@[simp,simp_core]
theorem pure_mean (x : X) : (pure (f:=Rand) x).mean = x := by simp[mean]

@[rand_push_E]
theorem bind_mean (x : Rand X) (f : X → Rand Y) :
    (x >>= f).mean = x.E (fun x' => (f x').mean) := by simp[mean,rand_push_E]

@[simp, simp_core, rand_push_E]
theorem map_mean (f : X → Y) {r : Rand X} :
    (f <$> r).mean
    =
    r.E f := by simp[mean]

set_option linter.unusedVariables false in
theorem mean_affine (x : Rand X) (f : X → Y) (hf : IsAffineMap ℝ f) :
   f x.mean = (do let x' ← x; return (f x')).mean := sorry_proof

theorem mean_add  (x : Rand X) (x' : X) : x.mean + x' = (x  + x').mean :=
  mean_affine x (fun x'' => x'' + x') (by fun_prop)
theorem mean_add' (x : Rand X) (x' : X) : x' + x.mean = (x' +  x).mean := by
  have h : (x' + x) = (x + x') := by
    show (do let x'' ← x; pure (x' + x'')) = (do let x'' ← x; pure (x'' + x'))
    simp only [add_comm]
  rw [h, add_comm]
  exact mean_add x x'

end Mean

variable (R)
variable [Module R Y] [IsScalarTower ℝ R Y]
/-- Estimate expected value of `f x`. -/
def estimateE (n : ℕ) (x : Rand X) (f : X → Y) : Rand Y := do
  let mut y := (0:Y)
  for _ in [0:n] do
    let x' ← x
    y += f x'
  return ((1:R)/(n:R)) • y


-- is this right? Do I need `mean` there?
-- theorem estimateE_affine
--     [AddCommGroup X] [Module ℝ X] [Module R X] [IsScalarTower ℝ R X] [TopologicalSpace X]
--     (n : ℕ) (x : Rand X) (f : X → Y) (hf : IsAffineMap ℝ f) :
--     (estimateE R n x f).mean = f (estimateE R n x id).mean := sorry_proof

theorem E_eq_mean_estimateE (n : ℕ) (x : Rand X) (f : X → Y) :
    x.E f = (estimateE R n x f).mean := sorry_proof

-- what conditions do we need on `g`? Probably continuity?
theorem E_eq_limit_estimateE (x : Rand X) (f : X → Y) (g : Y → Z) :
    g (x.E f)
    =
    limit n → ∞,
      let y := (estimateE R n x f).mean
      g y := sorry_proof


variable {R}

end ExpectedValue


----------------------------------------------------------------------------------------------------
-- Probability density function --------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


variable
  {R} [RealScalar R]
  [MeasurableSpace X]
  [MeasurableSpace Y]


variable (R)
/-- Probability density function of `x` w.r.t. the measure `ν`. -/
noncomputable
def pdf (x : Rand X) (ν : Measure X := by volume_tac) : X → R :=
  fun x' => Scalar.ofReal R (Measure.rnDeriv x.ℙ ν x').toReal
variable {R}

@[simp,simp_core]
theorem pdf_wrt_self (x : Rand X) [LawfulRand x] : x.pdf R x.ℙ = 1 := sorry_proof

@[simp,simp_core]
theorem bind_pdf (ν : Measure Y) (x : Rand X) (f : X → Rand Y) :
    (x >>= f).pdf R ν = fun y => ∫ x', ((f x').pdf R ν y) ∂x.ℙ := by
  funext y; simp[Rand.pdf,Bind.bind]; sorry_proof

@[simp,simp_core]
theorem ite_pdf (c) [Decidable c] (t e : Rand X) (μ : Measure X) :
    (if c then t else e).pdf R μ = (if c then t.pdf R μ else e.pdf R μ) := by
  if h : c then
    simp [h]
  else
    simp [h]


----------------------------------------------------------------------------------------------------
-- Combine -----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

variable [MeasureSpace R]
variable (R)
@[inline] -- inlining seems to have quite implact on performance
def _root_.SciLean.uniformI [MeasureSpace R] : Rand R := {
  spec := default
    -- erase (fun φ => weakIntegral (volume.restrict (Set.Icc (0:R) (1:R))) φ )
  rand :=
    fun g => do
    let N := stdRange.2
    let (n,g) := stdNext g
    let y := (NatCast.natCast n : R) / (NatCast.natCast N : R)
    pure (y, g)
}
variable {R}

/-- Draw `x` with probability `1-θ` and `y` with probability `θ`. -/
def combine (x y : Rand X) (θ : R) : Rand X := do
  let θ' ← uniformI R
  if θ ≤ θ' then
    x
  else
    y

/-- `x +[θ] y` return random variable `(1-θ)*x + θ*y`.
In other words
- `x` is generated with probability `1-θ`
- `y` is generated with probability `θ` -/
scoped macro x:term:65 " +[" θ:term "] " y:term:64 : term => `(term| combine $x $y $θ)


open Lean Parser
@[app_unexpander Rand.combine] meta def unexpandRandCombine : Lean.PrettyPrinter.Unexpander
| `($(_) $x $y $θ) => do Pure.pure (← `(term| $x +[$θ] $y)).raw
| _ => throw ()


@[rand_simp]
theorem combine_pdf (x y : Rand X) (μ : Measure X) (θ : R) :
    (x +[θ] y).pdf R μ
    =
    fun x' => (1-θ) * x.pdf R μ x' + θ * y.pdf R μ x' := sorry_proof


----------------------------------------------------------------------------------------------------
