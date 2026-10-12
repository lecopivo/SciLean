module

public import Probly.Normal
public import Probly.Tactic

public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul

public import Batteries.Lean.Expr

@[expose] public section


open MeasureTheory ENNReal BigOperators Finset

namespace Probly

macro "simp'" : conv => `(conv| simp (config := {zeta:=false}) (disch:=sorry))


noncomputable
def test (θ : ℝ) : Rand ℝ :=
  let x ~ normal θ 2
  let y ~ normal (x*x) 1
  if y ≤ 3 then
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
    conv => 
      enter [2,x]
      rand_fdE_as_E (normal (x*x) 1)
    rand_fdE_as_E (normal θ 1)
    simp'
    rand_pull_E

