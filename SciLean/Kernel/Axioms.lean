/-
Copyright (c) 2024 SciLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import SciLean.Kernel.DType
import SciLean.Kernel.Ops
import SciLean.Kernel.Spec

namespace SciLean.Kernel

/-!
# Kernel Axioms

Axioms that connect the C kernel operations to their pure Lean specifications.
These form the "trust bridge" - we axiomatize that the C code computes
the same thing as the mathematical specification (modulo floating-point).

## Design

The axioms follow this pattern:
1. `interpret dt bytes` - Convert ByteArray to mathematical representation
2. `toByteArray dt vals` - Convert mathematical representation to ByteArray
3. `kernel_op_correct` - Axiom that kernel op = spec composed with interpretation

This allows proofs to work with the clean `Spec.*` definitions while
computation uses the fast C kernel.
-/

-- ============================================================================
-- Interpretation Functions (Axiomatized)
-- ============================================================================

/-- Interpret a ByteArray as a vector of reals.
    This is the semantic bridge from bytes to mathematics.
    Axiomatized because actual implementation depends on dtype. -/
axiom interpret (dt : DType) (bytes : ByteArray) (n : Nat)
    (h : bytes.size = n * dt.bytes := by native_decide) : Fin n → ℝ

/-- Convert a vector of reals to ByteArray.
    Inverse of `interpret`. -/
axiom toByteArray (dt : DType) (n : Nat) (v : Fin n → ℝ) : ByteArray

/-- Interpret a ByteArray as a matrix of reals. -/
axiom interpretMatrix (dt : DType) (bytes : ByteArray) (m n : Nat)
    (h : bytes.size = m * n * dt.bytes := by native_decide) : Fin m → Fin n → ℝ

/-- Convert a matrix of reals to ByteArray. -/
axiom toByteArrayMatrix (dt : DType) (m n : Nat) (A : Fin m → Fin n → ℝ) : ByteArray

-- ============================================================================
-- Roundtrip Axioms
-- ============================================================================

/-- Interpretation and serialization are inverses. -/
axiom interpret_toByteArray (dt : DType) (n : Nat) (v : Fin n → ℝ)
    (h : (toByteArray dt n v).size = n * dt.bytes) :
    interpret dt (toByteArray dt n v) n h = v

axiom toByteArray_interpret (dt : DType) (bytes : ByteArray) (n : Nat)
    (h : bytes.size = n * dt.bytes) :
    toByteArray dt n (interpret dt bytes n h) = bytes

-- ============================================================================
-- Core Correctness Axioms
-- These connect kernel FFI to mathematical specifications
-- ============================================================================

section CoreAxioms

variable (dt : DType)

/-- Addition kernel correctness. -/
axiom add_correct (a b : ByteArray) (n : Nat)
    (ha : a.size = n * dt.bytes) (hb : b.size = n * dt.bytes)
    (hout : (Typed.add dt a b).size = n * dt.bytes) :
    interpret dt (Typed.add dt a b) n hout =
    Spec.add_spec (interpret dt a n ha) (interpret dt b n hb)

/-- Subtraction kernel correctness. -/
axiom sub_correct (a b : ByteArray) (n : Nat)
    (ha : a.size = n * dt.bytes) (hb : b.size = n * dt.bytes)
    (hout : (Typed.sub dt a b).size = n * dt.bytes) :
    interpret dt (Typed.sub dt a b) n hout =
    Spec.sub_spec (interpret dt a n ha) (interpret dt b n hb)

/-- Multiplication kernel correctness. -/
axiom mul_correct (a b : ByteArray) (n : Nat)
    (ha : a.size = n * dt.bytes) (hb : b.size = n * dt.bytes)
    (hout : (Typed.mul dt a b).size = n * dt.bytes) :
    interpret dt (Typed.mul dt a b) n hout =
    Spec.mul_spec (interpret dt a n ha) (interpret dt b n hb)

/-- Negation kernel correctness. -/
axiom neg_correct (x : ByteArray) (n : Nat)
    (hx : x.size = n * dt.bytes)
    (hout : (Typed.neg dt x).size = n * dt.bytes) :
    interpret dt (Typed.neg dt x) n hout =
    Spec.neg_spec (interpret dt x n hx)

/-- Exp kernel correctness. -/
axiom exp_correct (x : ByteArray) (n : Nat)
    (hx : x.size = n * dt.bytes)
    (hout : (Typed.exp dt x).size = n * dt.bytes) :
    interpret dt (Typed.exp dt x) n hout =
    Spec.exp_spec (interpret dt x n hx)

-- Note: sum_correct axiom omitted due to Float/ℝ type mismatch.
-- The kernel returns Float, but Spec.sum_spec returns ℝ.
-- This can be addressed later by importing RealToFloat conversion utilities.

/-- GEMV kernel correctness: y = A @ x -/
axiom gemv_correct (A x : ByteArray) (m n : Nat)
    (hA : A.size = m * n * dt.bytes) (hx : x.size = n * dt.bytes)
    (hout : (Typed.gemv dt A x m n).size = m * dt.bytes) :
    interpret dt (Typed.gemv dt A x m n) m hout =
    Spec.gemv_spec (interpretMatrix dt A m n hA) (interpret dt x n hx)

/-- GEMM kernel correctness: C = A @ B -/
axiom gemm_correct (A B : ByteArray) (m k n : Nat)
    (hA : A.size = m * k * dt.bytes) (hB : B.size = k * n * dt.bytes)
    (hout : (Typed.gemm dt A B m k n).size = m * n * dt.bytes) :
    interpretMatrix dt (Typed.gemm dt A B m k n) m n hout =
    Spec.gemm_spec (interpretMatrix dt A m k hA) (interpretMatrix dt B k n hB)

/-- Transpose kernel correctness. -/
axiom transpose_correct (src : ByteArray) (m n : Nat)
    (hs : src.size = m * n * dt.bytes)
    (hout : (Typed.transpose dt src m n).size = n * m * dt.bytes) :
    interpretMatrix dt (Typed.transpose dt src m n) n m hout =
    Spec.transpose_spec (interpretMatrix dt src m n hs)

end CoreAxioms

-- ============================================================================
-- Using the Axioms
-- ============================================================================

/-!
## How to Use These Axioms

1. **Proving kernel properties**: Use spec theorems + correctness axioms
   ```
   theorem kernel_gemm_assoc : ... := by
     rw [gemm_correct, gemm_correct, Spec.gemm_spec_assoc]
   ```

2. **AD rules**: Derive from spec + correctness
   - Forward: `d/dx (A @ x) = A @ dx` via `gemv_correct` + `Spec.gemv_spec_linear`
   - Reverse: `∇_x (A @ x) = Aᵀ @ dy` via `transpose_correct` + `gemv_correct`

3. **Verification**: Properties proven about Spec.* automatically apply to kernel
   via the correctness axioms (modulo floating-point).
-/

end SciLean.Kernel
