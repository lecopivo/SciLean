import SciLean.Analysis.SpecialFunctions.Exp
import SciLean.Analysis.SpecialFunctions.Log
import SciLean.Analysis.SpecialFunctions.Norm2

import SciLean.Analysis.Calculus.FDeriv

import SciLean.Tactic.Autodiff

open ComplexConjugate

namespace SciLean

set_option deprecated.oldSectionVars true

variable
  {R C} [Scalar R C] [RealScalar R]
  {W} [Vec R W]
  {U} [SemiHilbert R U]

set_default_scalar R

----------------------------------------------------------------------------------------------------
-- Gaussian ----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

open Scalar RealScalar in
def gaussian {U} [Sub U] [SMul R U] [Inner R U] (μ : U) (σ : R) (x : U) : R :=
  let x' := σ⁻¹ • (x - μ)
  1/(σ*sqrt (2*(pi : R))) * exp (- ‖x'‖₂²/2)


open Scalar RealScalar in
@[simp, simp_core]
theorem log_gaussian (μ : U) (σ : R) (x : U) :
    log (gaussian μ σ x)
    =
    let x' := σ⁻¹ • (x - μ)
    (- ‖x'‖₂²/2 - log σ - log (sqrt (2*(pi :R)))) := by

  unfold gaussian
  simp [log_inv,log_mul,log_div,log_exp,log_one]
  ring

def_fun_prop with_transitive
    {X : Type _} [NormedAddCommGroup X] [AdjointSpace R X] (σ : R) :
    Differentiable R (fun (μx : X×X) => gaussian μx.1 σ μx.2) by
  unfold gaussian; fun_prop

def_fun_prop with_transitive
    {X : Type _} [SemiHilbert R X] (σ : R) :
    HasAdjDiff R (fun (μx : X×X) => gaussian μx.1 σ μx.2) by
  unfold gaussian; fun_prop


section OnAdjointSpace

set_option deprecated.oldSectionVars true

variable {U : Type _} [NormedAddCommGroup U] [AdjointSpace R U] [CompleteSpace U]

@[fun_trans]
theorem gaussian.arg_μx.fderiv_rule (σ : R) :
    fderiv R (fun μx : U×U => gaussian μx.1 σ μx.2)
    =
    fun μx => fun dμx =>L[R]
      let dx' := - (σ^2)⁻¹ * ⟪dμx.2-dμx.1, μx.2-μx.1⟫
      dx' * gaussian μx.1 σ μx.2 := by
  ext x dx <;>
   (unfold gaussian; simp
    conv => lhs; autodiff
    simp[smul_pull]
    ring)


@[fun_trans]
theorem gaussian.arg_μx.fwdFDeriv_rule (σ : R) :
    fwdFDeriv R (fun μx : U×U => gaussian μx.1 σ μx.2)
    =
    fun μx  dμx =>
      let x' := gaussian μx.1 σ μx.2
      let dx' := - (σ^2)⁻¹ * ⟪dμx.2-dμx.1, μx.2-μx.1⟫
      (x', dx' * x') := by
  unfold fwdFDeriv
  fun_trans


@[fun_trans]
theorem gaussian.arg_μx.revFDeriv_rule (σ : R) :
    revFDeriv R (fun μx : U×U => gaussian μx.1 σ μx.2)
    =
    fun μx =>
      let s := gaussian μx.1 σ μx.2
      (s, fun dr =>
        let dx := (dr * s * (σ^2)⁻¹) • (μx.1-μx.2)
        (- dx, dx)) := by
  unfold revFDeriv
  funext μx; simp; funext dr
  fun_trans [smul_smul,neg_push];
  ring_nf
  simp [smul_sub,neg_sub]

end OnAdjointSpace
