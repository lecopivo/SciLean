import Mathlib.Data.Erased
import Mathlib.Control.Random
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Decomposition.Lebesgue

import SciLean.Core.Objects.Scalar
import SciLean.Core.Integral.CIntegral
import SciLean.Core.Rand.SimpAttr

import Mathlib.MeasureTheory.Measure.GiryMonad

open MeasureTheory ENNReal BigOperators Finset

namespace SciLean

abbrev erase (a : α) : Erased α := .mk a

@[simp,ftrans_simp]
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
@[pp_dot]
noncomputable
def ℙ {X} [MeasurableSpace X] (r : Rand X) : Measure X :=
  if h : r.spec.out.IsMeasure then
    choose h
  else
    0

/-- Specification of `x : Rand X` is really saying that it is a probability measure. -/
class LawfulRand (x : Rand X) [MeasurableSpace X] where
  is_measure : x.spec.out.IsMeasure
  is_prob : IsProbabilityMeasure x.ℙ

variable {X Y Z : Type _}
  [MeasurableSpace X]
  [MeasurableSpace Y]

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
    spec := erase (fun φ => x.spec.out (fun x => (f x).spec.out φ)),
    rand := bind x.rand (fun x => (f x).rand)
  }


instance : LawfulMonad Rand where
  bind_pure_comp := by intros; rfl
  bind_map       := by intros; rfl
  pure_bind      := by intros; ext; simp[Bind.bind,Pure.pure]
  bind_assoc     := by intros; ext; simp[Bind.bind,Pure.pure]
  map_const      := by intros; ext; rfl
  id_map         := by intros; ext; simp[Bind.bind,Pure.pure,id,Functor.map]
  seqLeft_eq     := by intros; ext; simp[Bind.bind,Pure.pure,Seq.seq,Function.const,Functor.map,SeqLeft.seqLeft]
  seqRight_eq    := by intros; ext; simp[Bind.bind,Pure.pure,Seq.seq,Function.const,Functor.map,SeqRight.seqRight]
  pure_seq       := by intros; ext; simp[Bind.bind,Pure.pure,Seq.seq,Functor.map]


-- this needs some integrability and lawfulness of Rand
theorem swap_bind (f : X → Y → Z) (x : Rand X) (y : Rand Y) :
    (do let x' ← x; let y' ← y; pure (f x' y'))
    =
    (do let y' ← y; let x' ← x; pure (f x' y')) := by
  sorry_proof


@[simp, ftrans_simp]
theorem pure_ℙ (x : X) : (pure x : Rand X).ℙ = Measure.dirac x := sorry_proof


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

@[pp_dot]
abbrev map (r : Rand X) (f : X → Y) : Rand Y := do
  let x' ← r
  return f x'

/-- Marginal distribution for the first component of a pair. -/
@[pp_dot]
abbrev fst (r : Rand (X×Y)) : Rand X := do
  let (x,_) ← r
  return x

/-- Marginal distribution for the second component of a pair. -/
@[pp_dot]
abbrev snd (r : Rand (X×Y)) : Rand Y := do
  let (_,y) ← r
  return y


@[simp, ftrans_simp]
theorem map_ℙ  (r : Rand X) (f : X → Y) :
  (r.map f).ℙ = r.ℙ.map f := sorry_proof


----------------------------------------------------------------------------------------------------
-- Expected Value ----------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section ExpectedValue

variable
  {R} [RealScalar R]
  [AddCommGroup Y] [Module ℝ Y]
  [AddCommGroup Z] [Module ℝ Z]
  -- [AddCommGroup U] [TopologicalSpace U] [TopologicalAddGroup U] [Module ℝ U] [LocallyConveUSpace ℝ U]
  {U} [AddCommGroup U] [Module ℝ U]

@[pp_dot]
noncomputable
def 𝔼 (r : Rand X) (φ : X → Y) : Y := ∫' x, φ x ∂r.ℙ

@[simp, ftrans_simp, rand_push_E]
theorem pure_𝔼 (x : X) (φ : X → Y) :
    (pure (f:=Rand) x).𝔼 φ = φ x := by simp [𝔼]

-- What are the right assumptions here? Lambda lawfulness of `x` and `f x'` and integrability of `φ`
@[rand_push_E]
theorem bind_E (r : Rand X) (f : X → Rand Y) (φ : Y → Z) :
    (r >>= f).𝔼 φ = r.𝔼 (fun x' => (f x').𝔼 φ) := by simp[𝔼]; sorry_proof

-- todo: We might want this to hold without lawfulness
-- consider adding as a property inside of `Distribution` or `Rand`
@[simp, ftrans_simp, rand_push_E]
theorem E_zero (r : Rand X) :
    r.𝔼 (fun _ => (0 : U)) = 0 := by simp[𝔼]

@[simp, ftrans_simp, add_pull, rand_push_E]
theorem E_add (r : Rand X) (φ ψ : X → U)
    (hφ : CIntegrable φ r.ℙ) (hψ : CIntegrable ψ r.ℙ) :
    r.𝔼 (fun x => φ x + ψ x) = r.𝔼 φ + r.𝔼 ψ := by
  simp[𝔼]; rw[cintegral_add] <;> assumption

@[simp, ftrans_simp, smul_pull, rand_push_E]
theorem E_smul (r : Rand X) (φ : X → ℝ) (y : Y) :
    r.𝔼 (fun x' => φ x' • y) = r.𝔼 φ • y := by sorry_proof


section Mean

variable [AddCommGroup X] [Module ℝ X]

noncomputable
def mean (r : Rand X) : X := r.𝔼 id

@[rand_pull_E]
theorem expectedValue_as_mean (x : Rand X) (φ : X → Y) :
    x.𝔼 φ = (x.map φ).mean := by
  simp [bind,mean,pure,𝔼]

@[simp,ftrans_simp]
theorem pure_mean (x : X) : (pure (f:=Rand) x).mean = x := by simp[mean]

@[rand_push_E]
theorem bind_mean (x : Rand X) (f : X → Rand Y) :
    (x >>= f).mean = x.𝔼 (fun x' => (f x').mean) := by simp[mean,rand_push_E]

theorem mean_add  (x : Rand X) (x' : X) : x.mean + x' = (x  + x').mean := by
  simp[HAdd.hAdd,mean,𝔼,pure,bind]; sorry_proof
theorem mean_add' (x : Rand X) (x' : X) : x' + x.mean = (x' +  x).mean := by
  simp[HAdd.hAdd,mean,𝔼,pure,bind]; sorry_proof

end Mean

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

@[simp,ftrans_simp]
theorem pdf_wrt_self (x : Rand X) [LawfulRand x] : x.pdf R x.ℙ = 1 := sorry_proof

@[simp,ftrans_simp]
theorem bind_pdf (ν : Measure Y) (x : Rand X) (f : X → Rand Y) :
    (x >>= f).pdf R ν = fun y => ∫ x', ((f x').pdf R ν y) ∂x.ℙ := by
  funext y; simp[Rand.pdf,Bind.bind,Pure.pure]; sorry_proof

@[simp,ftrans_simp]
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
def _root_.SciLean.uniformI : Rand R := {
  spec :=
    erase (fun φ => ∫' x in Set.Icc (0:R) (1:R), φ x)
  rand :=
    fun g => do
    let N := stdRange.2
    let (n,g) := stdNext g
    let y := (NatCast.natCast n : R) / (NatCast.natCast N : R)
    pure (y, g)
}
variable {R}

def combine (x y : Rand X) (θ : R) : Rand X := {
  spec := erase (fun φ => (Scalar.toReal R (1-θ)) • x.𝔼 φ + (Scalar.toReal R θ) • y.𝔼 φ)
  rand := fun g => do
    let (θ',g) := (uniformI R).rand g
    if θ' ≤ θ then
      y.rand g
    else
      x.rand g
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


@[rand_simp]
theorem combine_pdf (x y : Rand X) (μ : Measure X) (θ : R) :
    (x +[θ] y).pdf R μ
    =
    fun x' => (1-θ) * x.pdf R μ x' + θ * y.pdf R μ x' := sorry_proof


----------------------------------------------------------------------------------------------------
