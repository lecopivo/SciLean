import SciLean.Core.FunctionTransformations
import SciLean.Core.Functions.Exp
import SciLean.Tactic.Autodiff
-- import SciLean.Core.Meta.GenerateRevDeriv

open ComplexConjugate

namespace SciLean

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
@[simp, ftrans_simp]
theorem log_gaussian (μ : U) (σ : R) (x : U) :
    log (gaussian μ σ x)
    =
    let x' := σ⁻¹ • (x - μ)
    (- ‖x'‖₂²/2 - log σ - log (sqrt (2*(pi :R)))) := by

  unfold gaussian
  simp [log_inv,log_mul,log_div,log_exp,log_one]
  ring


-- TODO: add deriving statements!!!
-- derive_cdifferentiable_at gaussian μ x by unfold gaussian; fun_prop
-- derive_cdifferentiable gaussian μ x

-- derive_cdifferentiable_at gaussian μ σ x
--   assuming σ ≠ 0

-- -- this can't have non-compositional version
-- derive_cdifferentiable gaussian μ σ x
--   assuming σ ≠ 0

set_option linter.unusedVariables false in
@[fun_prop]
theorem gaussian.arg_μx.DifferentiableAt_rule
    {W} [NormedAddCommGroup W] [NormedSpace R W]
    {U} [NormedAddCommGroup U] [AdjointSpace R U]
    (μ : W → U) (σ : R) (x : W → U) (w : W)
    (hμ : DifferentiableAt R μ w) (hx : DifferentiableAt R x w) :
    DifferentiableAt R (fun w => gaussian (μ w) σ (x w)) w := by

  unfold gaussian
  sorry_proof -- fun_prop

@[fun_prop]
theorem gaussian.arg_μx.Differentiable_rule
    {W} [NormedAddCommGroup W] [NormedSpace R W]
    {U} [NormedAddCommGroup U] [AdjointSpace R U]
    (μ : W → U) (σ : R) (x : W → U)
    (hμ : Differentiable R μ) (hx : Differentiable R x) :
    Differentiable R (fun w => gaussian (μ w) σ (x w)) := by intro w; fun_prop


@[fun_prop]
theorem gaussian.arg_μx.CDifferentiableAt_rule (w : W)
    (μ : W → U) (σ : R) (x : W → U)
    (hμ : CDifferentiableAt R μ w) (hx : CDifferentiableAt R x w) :
    CDifferentiableAt R (fun w => gaussian (μ w) σ (x w)) w := by

  unfold gaussian
  fun_prop


@[fun_prop]
theorem gaussian.arg_μx.CDifferentiable_rule
    (μ : W → U) (σ : R) (x : W → U)
    (hμ : CDifferentiable R μ) (hx : CDifferentiable R x) :
    CDifferentiable R (fun w => gaussian (μ w) σ (x w)) := by

  intro w
  fun_prop


set_option linter.unusedVariables false in
@[fun_trans]
theorem gaussian.arg_μx.cderiv_rule
    (μ : W → U) (σ : R) (x : W → U)
    (hμ : CDifferentiable R μ) (hx : CDifferentiable R x) :
    fwdDeriv R (fun w => gaussian (μ w) σ (x w))
    =
    fun w dw =>
      let μdμ := fwdDeriv R μ w dw
      let xdx := fwdDeriv R x w dw
      let xdx' := σ⁻¹ • (xdx - μdμ)
      let g := gaussian μdμ.1 σ xdx.1
      (g, - ⟪xdx'.1, xdx'.2⟫ * g) := by

  sorry_proof


@[fun_prop]
theorem gaussian.arg_μσx.CDifferentiableAt_rule (w : W)
    (μ : W → U) (σ : W → R) (x : W → U)
    (hμ : CDifferentiableAt R μ w) (hσ : CDifferentiableAt R σ w) (hx : CDifferentiableAt R x w)
    (hσ' : σ w ≠ 0) :
    CDifferentiableAt R (fun w => gaussian (μ w) (σ w) (x w)) w := by

  unfold gaussian
  fun_prop (disch:=first | assumption | sorry_proof)

@[fun_prop]
theorem gaussian.arg_μσx.CDifferentiable_rule
    (μ : W → R) (σ : W → R) (x : W → R)
    (hμ : CDifferentiable R μ) (hσ : CDifferentiable R σ) (hx : CDifferentiable R x)
    (hσ' : ∀ w, σ w ≠ 0) :
    CDifferentiable R (fun w => gaussian (μ w) (σ w) (x w)) := by

  intro x
  fun_prop (disch:=aesop)
