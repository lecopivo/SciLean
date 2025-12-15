/-
Copyright (c) 2024 SciLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import SciLean.Kernel.DType

namespace SciLean.Kernel

/-!
# Kernel Operations

Opaque FFI bindings to the dtype-parametric C kernel.
All operations work on ByteArray with an explicit DType parameter.
-/

-- ============================================================================
-- Tier 0: Memory Operations
-- ============================================================================

/-- Copy n elements from src to dst. -/
@[extern "k_copy"]
opaque copy (dst : ByteArray) (src : @& ByteArray) (n : USize) (dt : UInt8) : ByteArray

-- ============================================================================
-- Tier 1: Elementwise Binary Operations
-- ============================================================================

/-- Elementwise addition: dst = a + b -/
@[extern "k_add"]
opaque add (dst : ByteArray) (a : @& ByteArray) (b : @& ByteArray)
           (n : USize) (dt : UInt8) : ByteArray

/-- Elementwise subtraction: dst = a - b -/
@[extern "k_sub"]
opaque sub (dst : ByteArray) (a : @& ByteArray) (b : @& ByteArray)
           (n : USize) (dt : UInt8) : ByteArray

/-- Elementwise multiplication: dst = a * b -/
@[extern "k_mul"]
opaque mul (dst : ByteArray) (a : @& ByteArray) (b : @& ByteArray)
           (n : USize) (dt : UInt8) : ByteArray

/-- Elementwise division: dst = a / b -/
@[extern "k_div"]
opaque div (dst : ByteArray) (a : @& ByteArray) (b : @& ByteArray)
           (n : USize) (dt : UInt8) : ByteArray

-- ============================================================================
-- Tier 2: Elementwise Unary Operations
-- ============================================================================

/-- Elementwise negation: dst = -x -/
@[extern "k_neg"]
opaque neg (dst : ByteArray) (x : @& ByteArray) (n : USize) (dt : UInt8) : ByteArray

/-- Elementwise absolute value: dst = |x| -/
@[extern "k_abs"]
opaque abs (dst : ByteArray) (x : @& ByteArray) (n : USize) (dt : UInt8) : ByteArray

/-- Elementwise exponential: dst = exp(x) -/
@[extern "k_exp"]
opaque exp (dst : ByteArray) (x : @& ByteArray) (n : USize) (dt : UInt8) : ByteArray

/-- Elementwise logarithm: dst = log(x) -/
@[extern "k_log"]
opaque log (dst : ByteArray) (x : @& ByteArray) (n : USize) (dt : UInt8) : ByteArray

/-- Elementwise square root: dst = sqrt(x) -/
@[extern "k_sqrt"]
opaque sqrt (dst : ByteArray) (x : @& ByteArray) (n : USize) (dt : UInt8) : ByteArray

/-- Elementwise hyperbolic tangent: dst = tanh(x) -/
@[extern "k_tanh"]
opaque tanh (dst : ByteArray) (x : @& ByteArray) (n : USize) (dt : UInt8) : ByteArray

-- ============================================================================
-- Tier 3: Reductions
-- ============================================================================

/-- Sum of all elements. -/
@[extern "k_sum"]
opaque sum (x : @& ByteArray) (n : USize) (dt : UInt8) : Float

/-- Maximum element value. -/
@[extern "k_max"]
opaque max (x : @& ByteArray) (n : USize) (dt : UInt8) : Float

/-- Index of maximum element. -/
@[extern "k_argmax"]
opaque argmax (x : @& ByteArray) (n : USize) (dt : UInt8) : USize

-- ============================================================================
-- Tier 4: Contractions (THE hot path)
-- ============================================================================

/-- General matrix multiply: C[m,n] = alpha * A[m,k] @ B[k,n] + beta * C[m,n]
    Row-major layout, contiguous arrays. -/
@[extern "k_gemm"]
opaque gemm (C : ByteArray) (A : @& ByteArray) (B : @& ByteArray)
            (m k n : USize) (alpha beta : Float) (dt : UInt8) : ByteArray

/-- Matrix-vector multiply: y[m] = A[m,n] @ x[n] -/
@[extern "k_gemv"]
opaque gemv (y : ByteArray) (A : @& ByteArray) (x : @& ByteArray)
            (m n : USize) (dt : UInt8) : ByteArray

-- ============================================================================
-- Tier 5: Fused Operations
-- ============================================================================

/-- Numerically stable softmax: dst[i] = exp(x[i] - max(x)) / sum(exp(x - max(x))) -/
@[extern "k_softmax"]
opaque softmax (dst : ByteArray) (x : @& ByteArray) (n : USize) (dt : UInt8) : ByteArray

/-- Fused scaled addition: y = alpha*x + beta*y -/
@[extern "k_axpby"]
opaque axpby (y : ByteArray) (alpha : Float) (x : @& ByteArray)
             (beta : Float) (n : USize) (dt : UInt8) : ByteArray

-- ============================================================================
-- Tier 6: Index Permutation
-- ============================================================================

/-- Transpose 2D matrix: dst[j,i] = src[i,j] -/
@[extern "k_transpose"]
opaque transpose (dst : ByteArray) (src : @& ByteArray)
                 (rows cols : USize) (dt : UInt8) : ByteArray

/-- General axis permutation: perm[i] = which src axis becomes dst axis i -/
@[extern "k_permute"]
opaque permute (dst : ByteArray) (src : @& ByteArray)
               (ndim : USize) (shape : @& ByteArray) (perm : @& ByteArray)
               (dt : UInt8) : ByteArray

-- ============================================================================
-- Tier 7: Random Number Generation
-- ============================================================================

/-- Seed the RNG state. -/
@[extern "k_rng_seed"]
opaque rngSeed (seed : UInt64) : Unit

/-- Fill buffer with uniform random in [0, 1). -/
@[extern "k_rand_uniform"]
opaque randUniform (dst : ByteArray) (n : USize) (dt : UInt8) : ByteArray

/-- Fill buffer with standard normal (mean=0, std=1). -/
@[extern "k_rand_normal"]
opaque randNormal (dst : ByteArray) (n : USize) (dt : UInt8) : ByteArray

-- ============================================================================
-- High-level wrappers with DType instead of UInt8
-- ============================================================================

namespace Typed

/-- Allocate a ByteArray for n elements of given dtype. -/
def alloc (dt : DType) (n : Nat) : ByteArray :=
  ByteArray.mk (.replicate (dt.bytes * n) 0)

/-- Elementwise addition with typed DType. -/
def add (dt : DType) (a b : ByteArray) : ByteArray :=
  let n := a.size / dt.bytes
  Kernel.add (alloc dt n) a b n.toUSize dt.toUInt8

/-- Elementwise subtraction with typed DType. -/
def sub (dt : DType) (a b : ByteArray) : ByteArray :=
  let n := a.size / dt.bytes
  Kernel.sub (alloc dt n) a b n.toUSize dt.toUInt8

/-- Elementwise multiplication with typed DType. -/
def mul (dt : DType) (a b : ByteArray) : ByteArray :=
  let n := a.size / dt.bytes
  Kernel.mul (alloc dt n) a b n.toUSize dt.toUInt8

/-- Elementwise division with typed DType. -/
def div (dt : DType) (a b : ByteArray) : ByteArray :=
  let n := a.size / dt.bytes
  Kernel.div (alloc dt n) a b n.toUSize dt.toUInt8

/-- Elementwise negation with typed DType. -/
def neg (dt : DType) (x : ByteArray) : ByteArray :=
  let n := x.size / dt.bytes
  Kernel.neg (alloc dt n) x n.toUSize dt.toUInt8

/-- Elementwise exp with typed DType. -/
def exp (dt : DType) (x : ByteArray) : ByteArray :=
  let n := x.size / dt.bytes
  Kernel.exp (alloc dt n) x n.toUSize dt.toUInt8

/-- Elementwise log with typed DType. -/
def log (dt : DType) (x : ByteArray) : ByteArray :=
  let n := x.size / dt.bytes
  Kernel.log (alloc dt n) x n.toUSize dt.toUInt8

/-- Elementwise sqrt with typed DType. -/
def sqrt (dt : DType) (x : ByteArray) : ByteArray :=
  let n := x.size / dt.bytes
  Kernel.sqrt (alloc dt n) x n.toUSize dt.toUInt8

/-- Elementwise tanh with typed DType. -/
def tanh (dt : DType) (x : ByteArray) : ByteArray :=
  let n := x.size / dt.bytes
  Kernel.tanh (alloc dt n) x n.toUSize dt.toUInt8

/-- Sum reduction with typed DType. -/
def sum (dt : DType) (x : ByteArray) : Float :=
  let n := x.size / dt.bytes
  Kernel.sum x n.toUSize dt.toUInt8

/-- Max reduction with typed DType. -/
def max (dt : DType) (x : ByteArray) : Float :=
  let n := x.size / dt.bytes
  Kernel.max x n.toUSize dt.toUInt8

/-- Argmax with typed DType. -/
def argmax (dt : DType) (x : ByteArray) : Nat :=
  let n := x.size / dt.bytes
  (Kernel.argmax x n.toUSize dt.toUInt8).toNat

/-- Matrix multiply: C = A @ B where A is [m,k] and B is [k,n]. -/
def gemm (dt : DType) (A B : ByteArray) (m k n : Nat) : ByteArray :=
  let C := alloc dt (m * n)
  Kernel.gemm C A B m.toUSize k.toUSize n.toUSize 1.0 0.0 dt.toUInt8

/-- Matrix-vector multiply: y = A @ x where A is [m,n]. -/
def gemv (dt : DType) (A x : ByteArray) (m n : Nat) : ByteArray :=
  let y := alloc dt m
  Kernel.gemv y A x m.toUSize n.toUSize dt.toUInt8

/-- Softmax with typed DType. -/
def softmax (dt : DType) (x : ByteArray) : ByteArray :=
  let n := x.size / dt.bytes
  Kernel.softmax (alloc dt n) x n.toUSize dt.toUInt8

/-- Transpose 2D matrix. -/
def transpose (dt : DType) (src : ByteArray) (rows cols : Nat) : ByteArray :=
  let dst := alloc dt (rows * cols)
  Kernel.transpose dst src rows.toUSize cols.toUSize dt.toUInt8

/-- Fill with uniform random [0, 1). -/
def randUniform (dt : DType) (n : Nat) : ByteArray :=
  Kernel.randUniform (alloc dt n) n.toUSize dt.toUInt8

/-- Fill with standard normal. -/
def randNormal (dt : DType) (n : Nat) : ByteArray :=
  Kernel.randNormal (alloc dt n) n.toUSize dt.toUInt8

/-- Scaled vector addition: y = alpha*x + beta*y -/
def axpby (dt : DType) (alpha : Float) (x : ByteArray) (beta : Float) (y : ByteArray) : ByteArray :=
  let n := x.size / dt.bytes
  Kernel.axpby y alpha x beta n.toUSize dt.toUInt8

end Typed

end SciLean.Kernel
