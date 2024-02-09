import SciLean.Modules.Prob.Tactic
import SciLean.Modules.Prob.Distributions.Uniform

import Mathlib.Tactic.FieldSimp

import Mathlib.Lean.Expr

open MeasureTheory ENNReal BigOperators Finset

namespace SciLean.Prob


variable {R} [RealScalar R] [ToString R]


open Rand

def test1 (θ : R) : Rand R :=
  let x ~ (uniform θ (1+θ*θ))
  if x < 1/2 then
    Rand.pure (x*θ)
  else
    Rand.pure 0

def test1_mean (θ : R) := (test1 θ).mean
  rewrite_by
    unfold Rand.mean Rand.E test1
    simp'
    equals θ*(1/4 - θ*θ) / (2*(1-θ*θ-θ)) => /-I did on paper-/ sorry

def test1_dmean (θ : R) := (fwdFDeriv ℝ test1_mean θ 1).2
  rewrite_by
    unfold test1_mean
    rand_AD


def fdtest1 :=
  derive_mean_fwdDeriv R :
    (fun θ : R => test1 θ)
  by
    enter [θ,dθ]; dsimp
    unfold test1

    rand_AD
    rand_push_E
    rand_fdE_as_E R, ((uniform θ (1 + θ*θ))
                      +[(1/2:R)]
                      (Rand.pure θ +[(1/2:R)] Rand.pure (1 + θ*θ)))
    simp'
    rand_pull_E


#eval show IO Unit from do

  let θ : Float := 0.2
  let n := 100000

  IO.println s!"Exact value:             {test1_mean θ}, {test1_dmean θ}"
  print_mean_variance (fdtest1 θ 1.0) n " for v1"



#exit

def test2 (θ : R) : Rand R :=
  let x ~ (uniform θ (1+θ*θ))
  if x < 1/2 then
    let y ~ (uniform x (x+1))
    Rand.pure (y+θ+x)
  else
    let y ~ (uniform (x+θ) (x+θ+10))
    Rand.pure (y+θ)


def fdtest2 :=
  derive_mean_fwdDeriv R :
    (fun θ : R => test2 θ)
  by
    enter [θ,dθ]; dsimp
    unfold test2

    rand_AD
    rand_push_E
    conv =>
      enter [2,x']
      rw[FDRand.fdE'_as_E_simple]
      rand_fdE_as_E R, ((uniform (x' + θ) (x' + θ + 10))
                        +[(1/2:R)]
                        (Rand.pure (x' + θ) +[(1/2:R)] Rand.pure (x' + θ + 10)))

    rand_fdE_as_E R, ((uniform θ (1 + θ*θ))
                      +[(1/2:R)]
                      (Rand.pure θ +[(1/2:R)] Rand.pure (1 + θ*θ)))

    simp'
    rand_pull_E
