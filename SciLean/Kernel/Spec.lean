/-
Copyright (c) 2024 SciLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace SciLean.Kernel.Spec

/-!
# Kernel Specifications

Pure Lean reference implementations of kernel operations.
These are generic over a scalar type R with appropriate algebraic structure.

These specifications serve as:
1. Mathematical definitions of what each kernel op computes
2. Targets for correctness axioms (kernel = spec)
3. Foundation for proving algebraic laws and AD rules
-/

open Finset in

-- ============================================================================
-- Tier 1: Elementwise Binary Operations
-- ============================================================================

/-- Elementwise addition specification. -/
def add_spec [Add R] (a b : Fin n → R) : Fin n → R :=
  fun i => a i + b i

/-- Elementwise subtraction specification. -/
def sub_spec [Sub R] (a b : Fin n → R) : Fin n → R :=
  fun i => a i - b i

/-- Elementwise multiplication specification. -/
def mul_spec [Mul R] (a b : Fin n → R) : Fin n → R :=
  fun i => a i * b i

/-- Elementwise division specification. -/
def div_spec [Div R] (a b : Fin n → R) : Fin n → R :=
  fun i => a i / b i

-- ============================================================================
-- Tier 2: Elementwise Unary Operations
-- ============================================================================

/-- Elementwise negation specification. -/
def neg_spec [Neg R] (x : Fin n → R) : Fin n → R :=
  fun i => -x i

/-- Elementwise absolute value specification (for Real). -/
noncomputable def abs_spec (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => |x i|

-- Note: exp, log, sqrt, tanh require Real or Float
-- We define them for Real and axiomatize for Float

/-- Elementwise exponential specification (for Real). -/
noncomputable def exp_spec (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Real.exp (x i)

/-- Elementwise logarithm specification (for Real). -/
noncomputable def log_spec (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Real.log (x i)

/-- Elementwise square root specification (for Real). -/
noncomputable def sqrt_spec (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Real.sqrt (x i)

/-- Elementwise tanh specification (for Real). -/
noncomputable def tanh_spec (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Real.tanh (x i)

-- ============================================================================
-- Tier 3: Reductions
-- ============================================================================

/-- Sum reduction specification. -/
def sum_spec [AddCommMonoid R] (x : Fin n → R) : R :=
  ∑ i, x i

/-- Max reduction specification (for ordered types). -/
noncomputable def max_spec [LinearOrder R] [OrderBot R] (x : Fin n → R) : R :=
  Finset.univ.sup x

/-- Argmax specification - returns index of maximum element.
    Uses classical choice to pick the index with maximum value. -/
noncomputable def argmax_spec [LinearOrder R] (x : Fin n → R) (hn : 0 < n := by omega) : Fin n :=
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  Classical.choose (Finset.exists_max_image Finset.univ x Finset.univ_nonempty)

-- ============================================================================
-- Tier 4: Contractions
-- ============================================================================

/-- Matrix-vector multiply specification: y = A @ x
    A has shape [m, n], x has shape [n], result has shape [m]. -/
def gemv_spec [Semiring R] (A : Fin m → Fin n → R) (x : Fin n → R) : Fin m → R :=
  fun i => ∑ j, A i j * x j

/-- General matrix multiply specification: C = A @ B
    A has shape [m, k], B has shape [k, n], result has shape [m, n]. -/
def gemm_spec [Semiring R] (A : Fin m → Fin k → R) (B : Fin k → Fin n → R) : Fin m → Fin n → R :=
  fun i j => ∑ l, A i l * B l j

/-- Scaled general matrix multiply: C = α * A @ B + β * C -/
def gemm_scaled_spec [Semiring R] (α : R) (A : Fin m → Fin k → R) (B : Fin k → Fin n → R)
    (β : R) (C : Fin m → Fin n → R) : Fin m → Fin n → R :=
  fun i j => α * (∑ l, A i l * B l j) + β * C i j

-- ============================================================================
-- Tier 5: Fused Operations
-- ============================================================================

/-- Softmax specification (simple version without numerical stability).
    softmax(x)_i = exp(x_i) / sum(exp(x))
    Note: The C kernel uses the numerically stable version (subtracts max). -/
noncomputable def softmax_spec (x : Fin n → ℝ) : Fin n → ℝ :=
  let exp_x := fun i => Real.exp (x i)
  let sum_exp := ∑ i, exp_x i
  fun i => exp_x i / sum_exp

/-- Scaled vector addition: y = α*x + β*y -/
def axpby_spec [Semiring R] (α : R) (x : Fin n → R) (β : R) (y : Fin n → R) : Fin n → R :=
  fun i => α * x i + β * y i

-- ============================================================================
-- Tier 6: Index Permutation
-- ============================================================================

/-- Transpose specification: dst[j,i] = src[i,j] -/
def transpose_spec (src : Fin m → Fin n → R) : Fin n → Fin m → R :=
  fun j i => src i j

-- ============================================================================
-- Basic Algebraic Properties (provable in pure Lean)
-- ============================================================================

section Properties

variable [CommSemiring R]

/-- Addition is commutative. -/
theorem add_spec_comm (a b : Fin n → R) : add_spec a b = add_spec b a := by
  ext i; simp [add_spec, add_comm]

/-- Multiplication is commutative. -/
theorem mul_spec_comm (a b : Fin n → R) : mul_spec a b = mul_spec b a := by
  ext i; simp [mul_spec, mul_comm]

/-- GEMM associativity: (A @ B) @ C = A @ (B @ C) -/
theorem gemm_spec_assoc
    (A : Fin m → Fin k → R) (B : Fin k → Fin l → R) (C : Fin l → Fin n → R) :
    gemm_spec (gemm_spec A B) C = gemm_spec A (gemm_spec B C) := by
  ext i j
  simp only [gemm_spec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext x
  congr 1
  ext y
  ring

end Properties

/-- Transpose involution: (Aᵀ)ᵀ = A -/
theorem transpose_spec_invol (A : Fin m → Fin n → R) :
    transpose_spec (transpose_spec A) = A := by
  ext i j; simp [transpose_spec]

-- ============================================================================
-- AD-Related Properties
-- ============================================================================

section AD

variable [CommRing R]

/-- Derivative of GEMV with respect to x: d/dx (A @ x) = A -/
theorem gemv_spec_linear (A : Fin m → Fin n → R) :
    ∀ x dx : Fin n → R, gemv_spec A (add_spec x dx) = add_spec (gemv_spec A x) (gemv_spec A dx) := by
  intro x dx
  ext i
  simp [gemv_spec, add_spec, Finset.sum_add_distrib, mul_add]

/-- Outer product for weight gradients: x ⊗ y -/
def outer_spec (x : Fin m → R) (y : Fin n → R) : Fin m → Fin n → R :=
  fun i j => x i * y j

end AD

end SciLean.Kernel.Spec
