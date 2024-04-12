import SciLean

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


#check parDistribFwdDeriv

@[fun_trans]
theorem Rand.𝔼.arg_r.cderiv_rule' (r : W → Rand X) (f : W → X → Y)
  (hf : ∀ x, CDifferentiable R (f · x)) :
  cderiv R (fun w => (r w).𝔼 (f w))
  =
  fun w dw =>
    let dr := parDistribFwdDeriv (fun w => (r w).ℙ.toDistribution (R:=R)) w dw
    let df := fun x => fwdDeriv R (f · x) w dw
    dr.extAction df (fun rdr ⊸ fun ydy ⊸ rdr.1•ydy.2 + rdr.2•ydy.1) := sorry_proof



section hihi

variable
  {X : Type _} [SemiInnerProductSpace R X] [MeasurableSpace X]
  {W : Type _} [SemiInnerProductSpace R W]
  {Y : Type _} [SemiInnerProductSpace R Y] [Module ℝ Y]
  {U} [SemiHilbert R U] [MeasureSpace U]

noncomputable
def normalFDμ (μ : U) (σ : R) : 𝒟'(U,R×R) :=
  ⟨fun φ => (∫' x, φ x * gaussian μ σ x, ∫' x, φ x * ), sorry_proof⟩


@[fun_trans]
theorem Rand.𝔼.arg_r.revDeriv_rule' (r : W → Rand X) (f : W → X → Y)
  (hf : ∀ x, HasAdjDiff R (f · x)) :
  revDeriv R (fun w => (r w).𝔼 (f w))
  =
  fun w =>
    let dr := parDistribRevDeriv (fun w => (r w).ℙ.toDistribution (R:=R)) w
    let df := fun x => revDeriv' R (f · x) w
    dr.extAction df ⟨fun rdr => ⟨fun ydf => (rdr.1•ydf.1, fun dy => ydf.2 (rdr.1•dy) + rdr.2 ⟪ydf.1,dy⟫),sorry_proof⟩,sorry_proof⟩ := sorry_proof

end hihi


set_option trace.Meta.Tactic.simp.rewrite true in
/-- Compute derivative of `loss1` by directly differentiating KLDivergence -/
def loss1_deriv := (∂ θ : R, loss1 θ) rewrite_by
  unfold loss1
  unfold scalarCDeriv
  simp only [kldiv_elbo]  -- log P(X) - ELBO P(Z,X) Q(Z)
  autodiff
  unfold model1 guide1 ELBO
  simp (config:={zeta:=false}) only [ftrans_simp,Scalar.log_mul, Tactic.lift_lets_simproc]
  autodiff

#check SciLean.norm2_scalar

#check gaussian

#check normal (0:Float) 1

#check (normal 0.0 1.0).ℙ
#eval  (normal 0.0 1.0).get

#check Rand
