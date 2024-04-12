import SciLean

import SciLean.Core.Rand.ExpectedValue

import SciLean.Core.Distribution.Basic
import SciLean.Core.Distribution.ParametricDistribDeriv
import SciLean.Core.Distribution.ParametricDistribFwdDeriv
import SciLean.Core.Distribution.ParametricDistribRevDeriv
import SciLean.Core.Distribution.SurfaceDirac

import SciLean.Core.Functions.Gaussian

namespace SciLean

open Rand MeasureTheory

variable {R} [RealScalar R] [MeasureSpace R]

set_default_scalar R

----------------------------------------------------------------------------------------------------
-- Variational Inference - Test 1 ------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

def model1 : Rand (R×R) :=
  let v ~ normal (0:R) 5
  if 0 ≤ v then
    let obs ~ normal (1:R) 1
  else
    let obs ~ normal (-2:R) 1

-- likelihood
#check (fun v : R => model1.conditionFst v)
  rewrite_by
    unfold model1
    simp

-- pdf
#check (fun xy : R×R => model1.pdf R volume xy)
  rewrite_by
    unfold model1
    simp

-- posterior
#check (fun obs : R => model1.conditionSnd obs)
  rewrite_by
    simp[model1]

def guide1 (θ : R) : Rand R := normal θ 1

noncomputable
def loss1 (θ : R) : R := KLDiv (R:=R) (guide1 θ) (model1.conditionSnd 0)


---------------------
-- Score Estimator --
---------------------

-- set_option profiler true
-- set_option trace.Meta.Tactic.fun_trans true in
-- set_option trace.Meta.Tactic.simp.rewrite true in
open Scalar RealScalar in
/-- Compute derivative of `loss1` with score estimator -/
def loss1_deriv_score (θ : R) :=
  derive_random_approx
    (∂ θ':=θ, loss1 θ')
  by
    unfold loss1 scalarCDeriv guide1 model1
    simp only [kldiv_elbo]  -- rewrite KL divergence with ELBO
    autodiff                -- this removes the term with (log P(X))
    unfold ELBO             -- unfold definition of ELBO
    simp                    -- compute densities
    autodiff                -- run AD
    let_unfold dr           -- technical step to unfold one particular let binding
    simp (config:={zeta:=false}) only [normalFDμ_score] -- appy score estimatorx
    -- clean up code such that `derive_random_approx` macro gen generate estimator
    simp only [ftrans_simp]; rand_pull_E

#eval 0

#eval print_mean_variance (loss1_deriv_score (2.0)) 10000 " derivative of loss1 is"


------------------------------
-- Reparameterize Estimator --
------------------------------

-- set_option trace.Meta.Tactic.fun_trans true in
-- set_option trace.Meta.Tactic.simp.rewrite true in
open Scalar RealScalar in
def loss1_deriv_reparam (θ : R) :=
  derive_random_approx
    (∂ θ':=θ, loss1 θ')
  by
    unfold loss1 scalarCDeriv guide1 model1

    -- rewrite as derivative of ELBO
    simp only [kldiv_elbo]
    autodiff
    unfold ELBO

    -- compute densities
    simp (config:={zeta:=false}) only [ftrans_simp, Scalar.log_mul, Tactic.lift_lets_simproc]
    simp (config:={zeta:=false}) only [Tactic.if_pull]

    -- reparameterization trick
    conv =>
      pattern (cderiv _ _ _ _)
      enter[2,x]
      rw[Rand.reparameterize (fun y => y - x) sorry_proof]

    -- clean up
    autodiff; autodiff

    simp

    -- compute derivative as distributional derivatives
    simp (config:={zeta:=false}) only [Rand.𝔼_deriv_as_distribDeriv]

    -- compute distrib derivative
    simp (config:={zeta:=false}) only [ftrans_simp,Tactic.lift_lets_simproc]
    simp (config:={zeta:=false}) only [Tactic.if_pull]

    -- destroy let bindings
    simp

    autodiff
    unfold scalarGradient
    autodiff
