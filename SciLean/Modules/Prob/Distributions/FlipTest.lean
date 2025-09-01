import SciLean.Modules.Prob.Tactic
import SciLean.Modules.Prob.Distributions.Flip

import Mathlib.Tactic.FieldSimp

import Mathlib.Lean.Expr

open MeasureTheory ENNReal BigOperators Finset

namespace SciLean.Prob


-- variable {X} [SMul R X] [AddCommGroup X] [Module R X] [MeasurableSpace X]
variable {R} [RealScalar R] [ToString R]



def test (θ : R) : Rand R :=
  let b ~ (flip θ)
  if b then
    Rand.pure 0
  else
    Rand.pure (-θ/2)


def fdtest_v1 :=
  derive_mean_fwdDeriv R :
    (fun θ : R => test θ)
  by
    enter [θ,dθ]; dsimp
    unfold test

    rand_AD
    rand_push_E
    rand_fdE_as_E R, (flip θ)
    simp'
    rand_pull_E


def fdtest_v2 :=
  derive_mean_fwdDeriv R :
    (fun θ : R => test θ)
  by
    enter [θ,dθ]; dsimp
    unfold test

    rand_AD
    rand_push_E
    rand_fdE_as_E R, (flip ((θ+1/2)/2))
    simp'
    rand_pull_E


def fdtest_v1_mean (θ dθ : R) := (fdtest_v1 θ dθ).mean
  rewrite_by
    unfold fdtest_v1
    rand_compute_mean


def fdtest_v2_mean (θ dθ: R) := (fdtest_v2 θ dθ).mean
  rewrite_by
    unfold fdtest_v2
    rand_compute_mean


theorem fdtest_mean_v1_eq_theory (θ dθ : ℝ) (h : θ - 1 ≠ 0) :
    fdtest_v1_mean θ dθ = (θ * (θ - 1) /2, dθ * (θ - 1/2)) := by
  unfold fdtest_v1_mean
  field_simp (disch:=(first | aesop))
  constructor <;> ring

-- theorem fdtest_mean_v2_eq_theory (θ dθ : ℝ) (h : θ ≠ 3/2) :
--     fdtest_v2_mean θ dθ = (θ * (θ - 1) /2, dθ * (θ - 1/2)) := by
--   unfold fdtest_v2_mean
--   have : 2 * 2 - (θ * 2 + 1) ≠ 0 := by sorry
--   have : θ * 2 + 1 - 2 * 2 ≠ 0 := by sorry
--   field_simp (disch:=(first | aesop))
--   constructor <;> ring

-- theorem fdtest_mean_v1_eq_v2  (θ dθ : ℝ) (h : θ ≠ 1) (h' : θ ≠ 3/2) :
--     fdtest_v1_mean θ dθ = fdtest_v2_mean θ dθ := by
--   unfold fdtest_v1_mean fdtest_v2_mean
--   have : θ - 1 ≠ 0 := by sorry
--   have : 2 * 2 - (θ * 2 + 1) ≠ 0 := sorry
--   have : θ * 2 + 1 - 2 * 2 ≠ 0 := sorry
--   field_simp (disch:=first | aesop)
--   constructor <;> ring


#eval show IO Unit from do

  let θ : Float := 0.8
  let n := 1000

  IO.println s!"Exact value:            {fdtest_v1_mean θ 1.0}"
  print_mean_variance (fdtest_v1 θ 1.0) n " for v1"
  print_mean_variance (fdtest_v2 θ 1.0) n " for v2"



noncomputable
def test2 (θ : R) : Rand R :=
  let b ~ (flip θ)
  if b then
    Rand.pure 0
  else
    let b' ~ (flip θ)
    if b' then
      Rand.pure (4*θ)
    else
      Rand.pure (-θ/2)

def fdtest2_v1 :=
  derive_mean_fwdDeriv R :
    (fun θ : R => test2 θ)
  by
    enter [θ,dθ]; dsimp
    unfold test2

    rand_AD
    rand_push_E
    rand_fdE_as_E R, (flip θ)
    simp'
    rand_pull_E


def fdtest2_v2 :=
  derive_mean_fwdDeriv R :
    (fun θ : R => test2 θ)
  by
    enter [θ,dθ]; dsimp
    unfold test2

    rand_AD
    rand_push_E
    rand_fdE_as_E R, (flip ((θ+1/2)/2))
    simp'
    rand_pull_E


def fdtest2_mean (θ dθ: R) := (fdtest2_v1 θ dθ).mean
  rewrite_by
    unfold fdtest2_v1
    rand_compute_mean


#eval show IO Unit from do

  let θ : Float := 0.8
  let n := 1000

  IO.println s!"Exact value:            {fdtest2_mean θ 1.0}"
  print_mean_variance (fdtest2_v1 θ 1.0) n " for v1"
  print_mean_variance (fdtest2_v2 θ 1.0) n " for v2"




def fdtest_v3 (ω : R) :=
  derive_mean_fwdDeriv R :
    (fun θ : R => test θ)
  by
    enter [θ,dθ]; dsimp
    unfold test

    rand_AD
    rand_push_E
    rand_fdE_as_E R, (flip ω)
    simp'
    rand_pull_E



/-- compute first and second moments of `fdtest_v3 ω θ`  -/
noncomputable
def fdtest_variance (ω θ : R) : Rand (R×R×R×R) :=
  let (y,dy) ~ fdtest_v3 ω θ 1
  Rand.pure (y*y, y, dy*dy, dy)


def fdtest_variance_fwdDeriv (θ : R) :=
  derive_mean_fwdDeriv R :
    (fun ω : R => fdtest_variance ω θ)
  by
    enter [ω,dω]; dsimp
    unfold fdtest_variance
    unfold fdtest_v3


    rand_AD --
    rand_push_E
    rand_fdE_as_E R, (flip ω)
    simp'
    rand_pull_E



#exit

/-- compute variance of `fdtest_v3 ω θ`  -/
noncomputable
def fdtest_variance (ω θ : R) : R×R :=

  let (y2, y, dy2, dy) := Rand.mean <|
    let (y,dy) ~ fdtest_v3 ω θ 1
    Rand.pure (y*y, y, dy*dy, dy)

  (y2 - y*y, dy2 - dy)


def fdtest_variance_fwdDeriv (θ : R) :=
  derive_rand_fwdDeriv
