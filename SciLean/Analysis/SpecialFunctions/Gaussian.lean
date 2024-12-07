import SciLean.Algebra.Dimension
import SciLean.Analysis.Calculus.FDeriv
import SciLean.Analysis.Calculus.ContDiff
import SciLean.Analysis.SpecialFunctions.Exp
import SciLean.Analysis.SpecialFunctions.Log
import SciLean.Analysis.SpecialFunctions.Norm2
import SciLean.Meta.GenerateFunTrans
import SciLean.Meta.Notation.Let'
import SciLean.Tactic.Autodiff
import SciLean.Lean.ToSSA

import Mathlib.Probability.Distributions.Gaussian

namespace SciLean

open Scalar RealScalar ComplexConjugate

set_option deprecated.oldSectionVars true

variable
  {R C} [Scalar R C] [RealScalar R]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X] {d : outParam ℕ} [hdim : Dimension R X d]

set_default_scalar R

----------------------------------------------------------------------------------------------------
-- Gaussian ----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

def gaussian [Dimension R X d] (μ : X) (σ : R) (x : X) : R :=
  let x' := σ⁻¹ • (x - μ)
  (2*π*σ^2)^(-(d:R)/2) * exp (- ‖x'‖₂²/2)

@[simp, simp_core]
theorem log_gaussian (μ : X) (σ : R) (x : X) :
    log (gaussian μ σ x)
    =
    let x' := σ⁻¹ • (x - μ)
    (- d/2 * (log (2*π) + 2 * log σ) - ‖x'‖₂²/2 ) := by

  unfold gaussian
  simp [log_push]
  ring


def_fun_prop gaussian in μ x with_transitive : Differentiable R


abbrev_fun_trans gaussian in μ x : fderiv R by
  equals (fun μx => fun dμx =>L[R]
            let' (μ,x) := μx
            let' (dμ,dx) := dμx
            let dx' := - (σ^2)⁻¹ * ⟪dx-dμ, x-μ⟫[R]
            dx' * gaussian μ σ x) =>
  unfold gaussian
  fun_trans
  funext x;
  ext dx <;> (simp[smul_pull]; ring)


abbrev_fun_trans gaussian in μ x : fwdFDeriv R by
  -- ideally
  -- unfold fwdFDeriv
  -- autodiff
  -- run common subexpression elimination
  equals (fun μx dμx =>
            let' (μ,x) := μx
            let' (dμ,dx) := dμx
            let dx' := - (σ^2)⁻¹ * ⟪dx-dμ, x-μ⟫[R]
            let G := gaussian μ σ x
            (G, dx' * G)) =>
  unfold fwdFDeriv
  fun_trans


abbrev_fun_trans gaussian in μ x [CompleteSpace X] : revFDeriv R by
  equals (fun μx =>
            let' (μ,x) := μx
            let G := gaussian μ σ x
            (G, fun dr =>
              let dx := (G*(σ^2)⁻¹*dr) • (x-μ)
              (dx,-dx))) =>
  unfold revFDeriv
  funext x; fun_trans
  funext dx; simp only [Prod.mk.injEq, neg_inj]
  constructor <;> module
