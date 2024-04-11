import SciLean

import SciLean.Core.Distribution.Basic
import SciLean.Core.Distribution.ParametricDistribDeriv

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


variable
  {W} [Vec R W]
  {X} [MeasurableSpace X] [Vec R X]
  {Y} [Vec R Y] [Module ℝ Y]

@[fun_trans]
theorem Rand.𝔼.arg_r.cderiv_rule (r : W → Rand X) (f : X → Y) :
  cderiv R (fun w => (r w).𝔼 f)
  =
  fun w dw =>
    let d := parDistribDeriv (fun w => (r w).ℙ.toDistribution (R:=R)) w dw
    d.extAction f (fun r ⊸ fun y ⊸ ((r • y) : Y)) := sorry_proof

set_option trace.Meta.Tactic.fun_trans true in

/-- Compute derivative of `loss1` by directly differentiating KLDivergence -/
def loss1_grad := (∂ θ : R, loss1 θ) rewrite_by
  unfold loss1
  unfold scalarCDeriv
  -- unfold scalarCDeriv
  -- rw[KLDiv.arg_P.cderiv_rule]

  -- fun_trans
  simp only [kldiv_elbo]
  fun_trans [Tactic.if_pull]
  unfold model1 guide1 ELBO
  fun_trans [Tactic.if_pull]
