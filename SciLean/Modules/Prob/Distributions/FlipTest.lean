import SciLean.Modules.Prob.Flip
import SciLean.Modules.Prob.Tactic

import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul

import Mathlib.Lean.Expr

open MeasureTheory ENNReal BigOperators Finset

namespace SciLean.Prob

macro "simp'" : conv => `(conv| simp (config := {zeta:=false}) (disch:=sorry))

variable {R} [RealScalar R]

noncomputable
def test (θ : ℝ) : Rand ℝ :=
  let b ~ (flip θ)
  if b then
    Rand.pure 0
  else
    Rand.pure (-θ/2)


noncomputable
def dtest :=
  derive_mean_fwdDeriv
    (fun θ => test θ)
  by
    enter [θ,dθ]; dsimp
    unfold test

    rand_AD
    rand_push_E
    rand_fdE_as_E (flip θ)
    -- rand_fdE_as_E (flip ((θ + 1/2)/2))
    simp'
    rand_pull_E



noncomputable
def _root_.Bool.toReal (b : Bool) : ℝ := if b then 1 else 0

noncomputable
def test2 (θ : ℝ) : Rand ℝ :=
  let b ~ (flip θ)
  if b then
    Rand.pure 0
  else
    let b' ~ (flip θ)
    if b' then
      Rand.pure (4*θ)
    else
      Rand.pure (-θ/2)


set_option trace.Meta.Tactic.simp.rewrite true in
noncomputable
def dtest2 :=
  derive_mean_fwdDeriv
    (fun θ => test2 θ)
  by
    enter [θ,dθ]; dsimp
    unfold test2

    rand_AD
    rand_push_E
    rand_fdE_as_E (flip θ)
    -- rand_fdE_as_E (flip ((θ + 1/2)/2))
    simp'
    rand_pull_E
