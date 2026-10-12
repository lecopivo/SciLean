module

public import SciLean.Algebra.Dimension
public import SciLean.Analysis.Calculus.FDeriv
public import SciLean.Analysis.Calculus.ContDiff
public import SciLean.Analysis.SpecialFunctions.Norm2
public import SciLean.Meta.GenerateFunTrans
public import SciLean.Meta.Notation.Let'
public import SciLean.Tactic.Autodiff
public import SciLean.Lean.ToSSA

public import SciLean.AD.Rules.Log
public import SciLean.AD.Rules.Exp

public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section
set_option linter.overlappingInstances false


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
theorem mul_pow_base_nat (x₁ x₂ : R) (n : ℕ) : x₁ ^ n * x₂ ^ n = (x₁ * x₂) ^ n := by ring

@[pow_push]
theorem pow_mul (x₁ x₂ y : R) : (x₁ * x₂) ^ y = x₁ ^ y * x₂ ^ y := (mul_pow_base x₁ x₂ y).symm

@[pow_push]
theorem pow_mul_nat (x₁ x₂ : R) (n : ℕ) : (x₁ * x₂) ^ n = x₁ ^ n * x₂ ^ n := by ring


theorem inv_eq_pow (x : R) : x⁻¹ = x ^ (-1:R) := by
  apply Scalar.toReal_injective
  rw [Scalar.toReal_rpow, Real.rpow_def]
  conv_lhs => rw [← Scalar.algebraMap_toReal x, ← map_inv₀, Scalar.toReal_algebraMap]
  conv_rhs => rw [← map_one (algebraMap ℝ R), ← map_neg, Scalar.toReal_algebraMap]
  rw [Complex.ofReal_neg, Complex.ofReal_one, Complex.cpow_neg_one, ← Complex.ofReal_inv,
    Complex.ofReal_re]
theorem pow_pow (x y₁ y₂ : R) : (x ^ y₁) ^ y₂ = x ^ (y₁*y₂) := sorry_proof

@[pow_pull]
theorem div_pow_base (x₁ x₂ y : R) : x₁ ^ y / x₂ ^ y = (x₁ / x₂) ^ y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_pow_base, inv_eq_pow, inv_eq_pow x₂, pow_pow, pow_pow,
    mul_comm y]

@[pow_pull]
theorem div_pow_base_nat (x₁ x₂ : R) (n : ℕ) : x₁ ^ n / x₂ ^ n = (x₁ / x₂) ^ n := by ring

@[pow_push]
theorem pow_div (x₁ x₂ y : R) : (x₁ / x₂) ^ y = x₁ ^ y / x₂ ^ y := (div_pow_base x₁ x₂ y).symm

@[pow_push]
theorem pow_div_nat (x₁ x₂ : R) (n : ℕ) : (x₁ / x₂) ^ n = x₁ ^ n / x₂ ^ n := by ring


@[exp_pull]
theorem mul_pow_power (x y₁ y₂ : R) : x ^ y₁ * x ^ y₂ = x ^ (y₁ + y₂) := sorry_proof

@[exp_push]
theorem pow_add_power (x y₁ y₂ : R) : x ^ (y₁ + y₂) = x ^ y₁ * x ^ y₂ := (mul_pow_power x y₁ y₂).symm


theorem sqrt_eq_pow (x : R) : Scalar.sqrt x = x ^ ((1:R)/2) := by
  apply Scalar.toReal_injective
  have h := Scalar.sqrt_def (K:=R) x
  simp only [RealScalar.is_real, implies_true, ↓reduceIte, Scalar.toComplex_eq_toReal,
    RCLike.re_to_complex, Complex.ofReal_re] at h
  rw [h, Scalar.toReal_rpow, Real.sqrt_eq_rpow]
  conv_rhs => rw [← map_one (algebraMap ℝ R), ← map_ofNat (algebraMap ℝ R) 2, ← map_div₀,
    Scalar.toReal_algebraMap]
theorem pow_pow_real_nat (x y : R) (n : ℕ) : (x ^ y) ^ n = x ^ (y*n) := sorry_proof
theorem pow_pow_nat_real (x y : R) (n : ℕ) : (x ^ n) ^ y = x ^ (n*y) := sorry_proof

@[simp, simp_core]
theorem pow_one (x : R) : x ^ (1:R) = x := by
  apply Scalar.toReal_injective
  rw [Scalar.toReal_rpow, Scalar.toReal_one, Real.rpow_one]

variable (n : ℕ) [Nat.AtLeastTwo n]

theorem pow_nat_to_real (x : R) (n : ℕ) [Nat.AtLeastTwo n] : x ^ n = x ^ (OfNat.ofNat n : R) := by
  apply Scalar.toReal_injective
  rw [Scalar.toReal_rpow]
  conv_lhs => rw [← Scalar.algebraMap_toReal x, ← map_pow, Scalar.toReal_algebraMap]
  conv_rhs => rw [← map_ofNat (algebraMap ℝ R), Scalar.toReal_algebraMap]
  rw [show (OfNat.ofNat n : ℝ) = ((n : ℕ) : ℝ) by norm_cast, Real.rpow_natCast]

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
  sorry_proof
