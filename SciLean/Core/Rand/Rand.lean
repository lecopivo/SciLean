import Mathlib.Data.Erased
import Mathlib.Control.Random

-- import SciLean.Modules.Prob.Init
-- import SciLean.Modules.Prob.Simps
-- import SciLean.Modules.Prob.Tactic
import SciLean.Core.Objects.Scalar
import SciLean.Core.Rand.Distribution
import SciLean.Core.Rand.SimpAttr

import Mathlib.MeasureTheory.Measure.GiryMonad

open MeasureTheory ENNReal BigOperators Finset

namespace SciLean.Prob



abbrev erase (a : α) : Erased α := .mk a

@[simp]
theorem erase_out {α} (a : α) : (erase a).out = a := by simp[erase]


/-- `x : Rand X` is a random variable of type `X`

You can draw a sample by `x.get : IO X`.
-/
structure Rand (X : Type _)  where
  /-- `spec` defines a probability measure using a generalized function

  Note: `Distribution X` is a set of generalized functions with domain `X`. It is not a probability distribution.
        Furthermore, any probability measure `μ` can be turned into a distribution `fun φ => ∫ x, φ x ∂μ`.

  Instead of `Measure X` we use `Distribution X`, this has two advantages:
    1. no requirement for `MeasurableSpace X` and thus we can provide `Monad Rand` instance
    2. we can get more generality with distributions when differentiating measure valued functions
  -/
  spec : Erased (Distribution X)
  rand : _root_.Rand X   -- ugh why doesn't mathlib have `Mathlib` namespace?

/-- Probability measure of a random variable -/
noncomputable
def Rand.ℙ {X} [TopologicalSpace X] (x : Rand X) := x.spec.out.measure

/-- Specification of `x : Rand X` is really saying that it is a probability measure. -/
class LawfulRand (x : Rand X) [TopologicalSpace X] where
  is_measure : x.spec.out.IsMeasure
  is_prob : IsProbabilityMeasure x.ℙ

variable {X} [TopologicalSpace X]

instance (x : Rand X) [inst : LawfulRand x] : IsProbabilityMeasure (x.ℙ) := inst.is_prob

variable {X Y Z : Type _}

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
axiom ext (x y : Rand X) : x.spec.out = y.spec.out → x = y


/-- Generate rundom number using IO randomness -/
def get (x : Rand X) : IO X := do
  let stdGen ← ULiftable.up IO.stdGenRef.get
  let (res, new) := x.rand stdGen
  let _ ← ULiftable.up (IO.stdGenRef.set new.down)
  pure res


----------------------------------------------------------------------------------------------------
-- Monadic structure -------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


instance : Monad Rand where
  pure {X} x := { spec := erase (pure x : Distribution X), rand := pure x }
  bind x f := { spec := erase (x.spec.out >>= fun x => (f x).spec.out), rand := bind x.rand (fun x => (f x).rand) }


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
-- Expected Value ----------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------



section ExpectedValue

variable
  {R} [RealScalar R]
  [NormedAddCommGroup X] [NormedSpace R X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace R Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [NormedSpace R Z] [NormedSpace ℝ Z] [CompleteSpace Z]



noncomputable
def E (x : Rand X) (φ : X → Y) : Y := ⟪x.spec.out, φ⟫

theorem E_as_integral (x : Rand X) [lr : LawfulRand x] (φ : X → Y) :
    x.E φ = ∫ x, φ x ∂x.ℙ := by
  simp [Rand.ℙ, Distribution.measure, lr.is_measure]
  have q := lr.is_measure
  rw[← Classical.choose_spec q φ]
  rfl

@[simp, rand_push_E]
theorem pure_E (x : X) (φ : X → Y) :
    (pure (f:=Rand) x).E φ = φ x := by simp [E,pure]

@[rand_push_E]
theorem bind_E (x : Rand X) (f : X → Rand Y) (φ : Y → Z) :
    (x >>= f).E φ = x.E (fun x' => (f x').E φ) := by simp[E,bind]

-- todo: We might want this to hold without lawfulness
-- consider adding as a property inside of `Distribution` or `Rand`
@[simp, rand_push_E]
theorem zero_E (x : Rand X) [LawfulRand x] :
    x.E (fun _ => (0 : Y)) = 0 := by simp[E_as_integral]

@[rand_simp,simp]
theorem add_E (x : Rand X) [LawfulRand x] (φ ψ : X → Y) (hφ : Integrable φ x.ℙ) (hψ : Integrable ψ x.ℙ) :
    x.E (fun x => φ x + ψ x) = x.E φ + x.E ψ := by
  simp[E_as_integral]; rw[integral_add] <;> assumption

-- we might add this to the definition of Rand and I think it won't require
-- integrability of `φ` nor lawfulness of `x`
theorem smul_E (x : Rand X) (φ : X → ℝ) (y : Y) :
    x.E (fun x' => φ x' • y) = x.E φ • y := by sorry

noncomputable
def mean (x : Rand X) : X := x.E id

@[rand_pull_E]
theorem expectedValue_as_mean (x : Rand X) (φ : X → Y) :
    x.E φ = (x >>=(fun x' => pure (φ x'))).mean := by
  simp [bind,mean,pure,E]


-- Again we might add this as a definit property of `Rand`
--  (It would not work for `Distribution` as integrating constant function yields that constant
--  only over a probability measure)
theorem mean_add  (x : Rand X) (x' : X) : x.mean + x' = (x  + x').mean := by
  simp[HAdd.hAdd,mean,E,pure,bind]; sorry_proof
theorem mean_add' (x : Rand X) (x' : X) : x' + x.mean = (x' +  x).mean := by
  simp[HAdd.hAdd,mean,E,pure,bind]; sorry_proof


end ExpectedValue


----------------------------------------------------------------------------------------------------
-- Probability density function --------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


variable
  (R) [RealScalar R]
  [TopologicalSpace X] -- [NormedAddCommGroup X] [NormedSpace R X] [NormedSpace ℝ X] [CompleteSpace X]
  [TopologicalSpace Y] -- [NormedAddCommGroup Y] [NormedSpace R Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  -- [NormedAddCommGroup Z] [NormedSpace R Z] [NormedSpace ℝ Z] [CompleteSpace Z]


-- variable (R) [RealScalar R]

-- variable
--   [NormedAddCommGroup X] [NormedSpace R X] [NormedSpace ℝ X] [CompleteSpace X]
--   [NormedAddCommGroup Y] [NormedSpace R Y] [NormedSpace ℝ Y] [CompleteSpace Y]
--   [NormedAddCommGroup Z] [NormedSpace R Z] [NormedSpace ℝ Z] [CompleteSpace Z]


/-- Probability density function of `x` w.r.t. the measure `ν`. -/
noncomputable
def pdf {X} [TopologicalSpace X] (x : Rand X) (ν : @Measure X (borel _)) : X → R :=
  fun x' => Scalar.ofReal R (Measure.rnDeriv x.ℙ ν x').toReal

variable {R}
-- noncomputable
-- abbrev rpdf (x : Rand X) (ν : @Measure X (borel _)) : X → ℝ :=
--   fun x' => x.pdf (lebesgue) ℝ ν x'

@[rand_simp,simp]
theorem pdf_wrt_self (x : Rand X) [LawfulRand x] : x.pdf R x.ℙ = 1 := sorry

-- @[rand_simp,simp]
-- theorem rpdf_wrt_self (x : Rand X) : x.rpdf x.ℙ = 1 := by
--   funext x; unfold rpdf; rw[pdf_wrt_self]

-- @[rand_simp,simp]
-- theorem bind_rpdf (ν : @Measure Y (borel _)) (x : Rand X) (f : X → Rand Y) :
--     (x.bind f).rpdf R ν = fun y => ∫ x', ((f x').rpdf ν y) ∂x.ℙ := by
--   funext y; simp[Rand.pdf,Rand.bind,Rand.pure]; sorry

@[rand_simp,simp]
theorem bind_pdf (ν : @Measure Y (borel _)) (x : Rand X) (f : X → Rand Y) :
    (x >>= f).pdf R ν = fun y => ∫ x', ((f x').pdf R ν y) ∂x.ℙ := by
  funext y; simp[Rand.pdf,Bind.bind,Pure.pure]; sorry

-- open Classical in
-- @[rand_simp,simp]
-- theorem pdf_wrt_add (x : Rand X) (μ ν : @Measure X (borel _)) :
--     x.pdf R (μ + ν)
--     =
--     fun x' =>
--       if x.ℙ ⟂ₘ μ then 0 else x.pdf R μ x'
--       +
--       if x.ℙ ⟂ₘ ν then 0 else x.pdf R ν x' := sorry


----------------------------------------------------------------------------------------------------
-- Combine -----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


def combine (x y : Rand X) (θ : R) : Rand X := {
  spec := erase ⟨fun φ => (Scalar.toReal R (1-θ)) • x.E φ + (Scalar.toReal R θ) • y.E φ⟩
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


@[rand_simp]
theorem combine_pdf (x y : Rand X) (μ : @Measure X (borel _)) (θ : R) :
    (x +[θ] y).pdf R μ
    =
    fun x' => (1-θ) * x.pdf R μ x' + θ * y.pdf R μ x' := sorry



----------------------------------------------------------------------------------------------------
#exit
variable (C : ℕ → Type) [∀ n, NormedAddCommGroup (C n)] [∀ n, NormedSpace ℝ (C n)] [∀ n, CompleteSpace (C n)]
variable (D : ℕ → Type) [∀ n, NormedAddCommGroup (D n)] [∀ n, NormedSpace ℝ (D n)] [∀ n, CompleteSpace (D n)]

-- under what condition is this true??? I think `f` has to be affine
theorem push_to_E (f : X → Rand Y) (x : Rand Z) (φ : Z → X) :
    (f (x.E φ)).E id = x.E (fun z => (f (φ z)).E id) := by
  conv => rand_pull_E
  simp[mean,id]
  unfold id
  conv => rand_push_E
  sorry

-- this requires that `f` is affine
theorem push_to_E' (f : X → Y) (x : Rand Z) (φ : Z → X) :
    (f (x.E φ)) = x.E (fun z => f (φ z)) := sorry

theorem E_induction (x₀ : C 0) (r : (n : Nat) → Rand (D n)) (f : (n : ℕ) → C n → D n → (C (n+1))) :
    Nat.recOn (motive:=C) n x₀ (fun n x => (r n).E (f n x))
    =
    (Nat.recOn (motive:=fun n => Rand (C n)) n (pure x₀) (fun n x => do let x' ← x; let y ← r n; pure (f n x' y))).mean := by
  induction n
  case zero => simp[mean]
  case succ n hn =>
    simp[hn,mean]
    conv => rand_pull_E
    simp
    conv =>
      lhs
      enter[1,2,x',1]
      unfold mean
      simp[push_to_E' (f:=(f n · x'))]



theorem E_induction (x₀ : C 0) (f : (n : ℕ) → C n → Rand (C (n+1))) :
    Nat.recOn (motive:=C) n x₀ (fun n x => (f n x).E id)
    =
    (Nat.recOn (motive:=fun n => Rand (C n)) n (pure x₀) (fun n x => do let x' ← x; f n x')).mean := by
  induction n
  case zero => simp[mean]
  case succ n hn =>
    simp[hn,mean]
    simp[push_to_E (f:=f n)]
    conv => rand_push_E
    simp
