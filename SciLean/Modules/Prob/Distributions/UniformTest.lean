import SciLean.Modules.Prob.Tactic
import SciLean.Modules.Prob.Distributions.Uniform

import Mathlib.Tactic.FieldSimp

import Mathlib.Lean.Expr

open MeasureTheory ENNReal BigOperators Finset

namespace SciLean.Prob


variable {R} [RealScalar R] [ToString R]


open Rand

def test (θ : R) : Rand R :=
  let x ~ (uniform θ (1+θ*θ))
  if x < 0.5 then
    let y ~ (uniform x (x+1))
    Rand.pure (y+θ+x)
  else
    let y ~ (uniform (x+θ) (x+θ+10))
    Rand.pure (y+θ)
#check ite


def fdtest_v1 :=
  derive_mean_fwdDeriv R :
    (fun θ : R => test θ)
  by
    enter [θ,dθ]; dsimp
    unfold test

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
