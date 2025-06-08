import SciLean.Algebra.Dimension
import SciLean.Analysis.Calculus.FDeriv
import SciLean.Analysis.Calculus.ContDiff
import SciLean.Analysis.SpecialFunctions.Norm2
import SciLean.Meta.GenerateFunTrans
import SciLean.Meta.Notation.Let'
import SciLean.Tactic.Autodiff
import SciLean.Lean.ToSSA

import SciLean.AD.Rules.Log
import SciLean.AD.Rules.Exp

import Mathlib.Probability.Distributions.Gaussian.Real

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





----------------------------------------------------------------------------------------------------


@[pow_pull]
theorem mul_pow_base (x₁ x₂ y : R) : x₁ ^ y * x₂ ^ y = (x₁ * x₂) ^ y := sorry_proof

@[pow_pull]
theorem mul_pow_base_nat (x₁ x₂ : R) (n : ℕ) : x₁ ^ n * x₂ ^ n = (x₁ * x₂) ^ n := sorry_proof

@[pow_push]
theorem pow_mul (x₁ x₂ y : R) : (x₁ * x₂) ^ y = x₁ ^ y * x₂ ^ y := sorry_proof

@[pow_push]
theorem pow_mul_nat (x₁ x₂ : R) (n : ℕ) : (x₁ * x₂) ^ n = x₁ ^ n * x₂ ^ n := sorry_proof


@[pow_pull]
theorem div_pow_base (x₁ x₂ y : R) : x₁ ^ y / x₂ ^ y = (x₁ / x₂) ^ y := sorry_proof

@[pow_pull]
theorem div_pow_base_nat (x₁ x₂ : R) (n : ℕ) : x₁ ^ n / x₂ ^ n = (x₁ / x₂) ^ n := sorry_proof

@[pow_push]
theorem pow_div (x₁ x₂ y : R) : (x₁ / x₂) ^ y = x₁ ^ y / x₂ ^ y := sorry_proof

@[pow_push]
theorem pow_div_nat (x₁ x₂ : R) (n : ℕ) : (x₁ / x₂) ^ n = x₁ ^ n / x₂ ^ n := sorry_proof


@[exp_pull]
theorem mul_pow_power (x y₁ y₂ : R) : x ^ y₁ * x ^ y₂ = x ^ (y₁ + y₂) := sorry_proof

@[exp_push]
theorem pow_add_power (x y₁ y₂ : R) : x ^ (y₁ + y₂) = x ^ y₁ * x ^ y₂ := sorry_proof


theorem sqrt_eq_pow (x : R) : Scalar.sqrt x = x ^ ((1:R)/2) := sorry_proof
theorem inv_eq_pow (x : R) : x⁻¹ = x ^ (-1:R) := sorry_proof
theorem pow_pow (x y₁ y₂ : R) : (x ^ y₁) ^ y₂ = x ^ (y₁*y₂) := sorry_proof
theorem pow_pow_real_nat (x y : R) (n : ℕ) : (x ^ y) ^ n = x ^ (y*n) := sorry_proof
theorem pow_pow_nat_real (x y : R) (n : ℕ) : (x ^ n) ^ y = x ^ (n*y) := sorry_proof

@[simp, simp_core]
theorem pow_one (x : R) : x ^ (1:R) = x := by sorry_proof

variable (n : ℕ) [Nat.AtLeastTwo n]

theorem pow_nat_to_real (x : R) (n : ℕ) [Nat.AtLeastTwo n] : x ^ n = x ^ (OfNat.ofNat n : R) := by sorry_proof

example (x₁ x₂ y : R) : x₁ ^ y * x₂ ^ y = (x₁ * x₂) ^ y := by simp [pow_pull]

-- source http://www.lucamartino.altervista.org/2003-003.pdf
-- set_option pp.numericTypes true in
theorem mul_gaussian_gaussian (μ₁ μ₂ : X) (σ₁ σ₂ : R) (x : X) :
    gaussian μ₁ σ₁ x * gaussian μ₂ σ₂ x
    =
    let s2  := σ₁*σ₁ + σ₂*σ₂
    let w₁ := σ₂*σ₂ * s2⁻¹
    let w₂ := σ₁*σ₁ * s2⁻¹
    let μ₁₂ := w₁•μ₁ + w₂•μ₂
    let σ₁₂ := Scalar.sqrt ((σ₁*σ₁) * (σ₂*σ₂) * s2⁻¹)
    let σ' := (σ₁*σ₂)/σ₁₂  -- √(σ₁^2 + σ₂^2)
    let S₁₂ := gaussian μ₁ σ' μ₂
    S₁₂ * gaussian μ₁₂ σ₁₂ x := by

  have h : ∀ a b c d : R, (a*b)*(c*d) = (a*c)*(b*d) := by intros; ring
  simp only [gaussian]
  conv => lhs; rw[h]
  conv => rhs; rw[h]
  simp only [exp_pull, pow_pull]

  have : 0 < σ₁ := sorry_proof
  have : 0 < σ₂ := sorry_proof

  apply congr
  apply congrArg


  · apply congrFun; apply congrArg
    simp only [div_eq_mul_inv]
    simp only [pow_push,inv_eq_pow,sqrt_eq_pow,
               pow_pow,pow_pow_nat_real,pow_pow_real_nat]
    norm_num
    generalize hβ : (σ₁ * σ₁ + σ₂ * σ₂) = β
    have : 0 < β := by rw[←hβ]; sorry_proof
    simp only [← inv_eq_pow, ←pow_nat_to_real]
    field_simp
    ring

  · apply congrArg

    generalize h   : (σ₁ * σ₁ * (σ₁ * σ₁ + σ₂ * σ₂)⁻¹) = c
    generalize h'' : (σ₂ * σ₂ * (σ₁ * σ₁ + σ₂ * σ₂)⁻¹) = e
    generalize h'   : sqrt (σ₁ * σ₁ * (σ₂ * σ₂) * (σ₁ * σ₁ + σ₂ * σ₂)⁻¹) = d

    simp only [norm2_def, smul_pull, sub_pull, add_pull]
    simp only [div_eq_mul_inv, inv_eq_pow, sqrt_eq_pow, pow_push, pow_pow]

    sorry_proof
