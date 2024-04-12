import SciLean

import SciLean.Core.Rand.ExpectedValue

import SciLean.Core.Distribution.Basic
import SciLean.Core.Distribution.ParametricDistribDeriv
import SciLean.Core.Distribution.ParametricDistribFwdDeriv
import SciLean.Core.Distribution.ParametricDistribRevDeriv

import SciLean.Core.Functions.Gaussian

namespace SciLean

open Rand MeasureTheory

variable {R} [RealScalar R] [MeasureSpace R]

set_default_scalar R

----------------------------------------------------------------------------------------------------
-- Variational Inference - Test 1 ------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

def model1 :=
  let v ~ normal (0:R) 5
  if v > 0 then
    let obs ~ normal (1:R) 1
  else
    let obs ~ normal (-2:R) 1

def guide1 (θ : R) := normal θ 1

noncomputable
def loss1 (θ : R) := KLDiv (R:=R) (guide1 θ) (model1.conditionSnd 0)

-- set_option profiler true
-- set_option trace.Meta.Tactic.fun_trans true in
-- set_option trace.Meta.Tactic.simp.rewrite true in

/-- Compute derivative of `loss1` by directly differentiating KLDivergence -/
def loss1_deriv (θ : R) :=
  derive_random_approx
    (∂ θ':=θ, loss1 θ')
  by
    unfold loss1
    unfold scalarCDeriv
    simp only [kldiv_elbo]
    autodiff
    unfold model1 guide1 ELBO
    simp (config:={zeta:=false}) only [ftrans_simp, Scalar.log_mul, Tactic.lift_lets_simproc]
    autodiff
    let_unfold dr
    simp (config:={zeta:=false,singlePass:=true}) only [normalFDμ_score]
    simp only [ftrans_simp]; rand_pull_E

#eval 0

#eval print_mean_variance (loss1_deriv (2.0)) 10000 " derivative of loss1 is"
