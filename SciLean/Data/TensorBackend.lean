/-
TensorBackend Typeclass for Device Abstraction

Inspired by tinygrad's device abstraction pattern.
Provides a unified interface for compute backends (CPU/BLAS, Metal, CUDA).

The key insight from tinygrad:
- Operations build a computation graph
- Graph is optimized before execution
- Backend dispatches to device-specific implementations
-/
import SciLean.Data.DataArray.DataArray
import SciLean.Data.DataArray.TensorOperations

namespace SciLean

/-! ## Backend Device Enumeration -/

/-- Compute device types -/
inductive Device where
  | cpu    -- CPU with BLAS
  | metal  -- Apple Metal GPU
  | cuda   -- NVIDIA CUDA (future)
  deriving BEq, Repr, Inhabited

/-! ## TensorBackend Typeclass -/

/-- Abstract tensor backend for device-agnostic operations.

Implementations provide device-specific optimized code.
The default implementations fall back to naive loops.
-/
class TensorBackend (B : Type) where
  /-- The device this backend targets -/
  device : Device

  /-- Allocate a zero-initialized buffer of n elements -/
  zeros : Nat → B

  /-- Copy data from one buffer to another -/
  copy : B → B

  /-- Element-wise addition: z = x + y -/
  add : B → B → B

  /-- Scalar multiplication: y = a * x -/
  scal : Float → B → B

  /-- Scalar addition: y = x + a -/
  adds : B → Float → B

  /-- Element-wise multiplication: z = x * y -/
  mul : B → B → B

  /-- Dot product: sum(x * y) -/
  dot : B → B → Float

  /-- Sum of all elements -/
  sum : B → Float

  /-- Maximum element -/
  max : B → Float

  /-- Matrix-vector multiply: y = A * x
      A is m×n stored row-major, x is n-dim, y is m-dim -/
  gemv : Nat → Nat → B → B → B

  /-- Matrix-matrix multiply: C = A * B
      A is m×k, B is k×n, C is m×n, all row-major -/
  gemm : Nat → Nat → Nat → B → B → B

  /-- GEMM with scaling: C = α*A*B + β*C -/
  gemmScaled : Nat → Nat → Nat → Float → B → B → Float → B → B

  /-- Element-wise exponential -/
  exp : B → B

  /-- Element-wise natural log -/
  log : B → B

  /-- Softmax along the last axis -/
  softmax : B → B

/-! ## CPU Backend (FloatArray with BLAS) -/

/-- CPU backend using FloatArray and BLAS operations -/
instance : TensorBackend FloatArray where
  device := .cpu

  zeros n := Id.run do
    let mut arr : FloatArray := .emptyWithCapacity n
    for _ in [0:n] do
      arr := arr.push 0.0
    arr

  copy src := src  -- FloatArray is already immutable/copy-on-write

  add x y := Id.run do
    let mut z : FloatArray := .emptyWithCapacity x.size
    for i in [0:x.size] do
      z := z.push (x.uget i.toUSize sorry_proof + y.uget i.toUSize sorry_proof)
    z

  scal a x := Id.run do
    let mut y : FloatArray := .emptyWithCapacity x.size
    for i in [0:x.size] do
      y := y.push (a * x.uget i.toUSize sorry_proof)
    y

  adds x a := Id.run do
    let mut y : FloatArray := .emptyWithCapacity x.size
    for i in [0:x.size] do
      y := y.push (x.uget i.toUSize sorry_proof + a)
    y

  mul x y := Id.run do
    let mut z : FloatArray := .emptyWithCapacity x.size
    for i in [0:x.size] do
      z := z.push (x.uget i.toUSize sorry_proof * y.uget i.toUSize sorry_proof)
    z

  dot x y := Id.run do
    let mut s := 0.0
    for i in [0:x.size] do
      s := s + x.uget i.toUSize sorry_proof * y.uget i.toUSize sorry_proof
    s

  sum x := Id.run do
    let mut s := 0.0
    for i in [0:x.size] do
      s := s + x.uget i.toUSize sorry_proof
    s

  max x := Id.run do
    if x.size == 0 then return -Float.inf
    let mut m := x.uget 0 sorry_proof
    for i in [1:x.size] do
      let v := x.uget i.toUSize sorry_proof
      if v > m then m := v
    m

  gemv m n A x := Id.run do
    let mut y : FloatArray := .emptyWithCapacity m
    for i in [0:m] do
      let mut s := 0.0
      for j in [0:n] do
        s := s + A.uget (i*n + j).toUSize sorry_proof * x.uget j.toUSize sorry_proof
      y := y.push s
    y

  gemm m k n A B := Id.run do
    let mut C : FloatArray := .emptyWithCapacity (m*n)
    for _ in [0:m*n] do
      C := C.push 0.0
    for i in [0:m] do
      for j in [0:n] do
        let mut s := 0.0
        for l in [0:k] do
          s := s + A.uget (i*k + l).toUSize sorry_proof * B.uget (l*n + j).toUSize sorry_proof
        C := C.uset (i*n + j).toUSize s sorry_proof
    C

  gemmScaled m k n alpha A B beta C := Id.run do
    let mut result : FloatArray := .emptyWithCapacity (m*n)
    for i in [0:m] do
      for j in [0:n] do
        let mut s := 0.0
        for l in [0:k] do
          s := s + A.uget (i*k + l).toUSize sorry_proof * B.uget (l*n + j).toUSize sorry_proof
        let cij := C.uget (i*n + j).toUSize sorry_proof
        result := result.push (alpha * s + beta * cij)
    result

  exp x := Id.run do
    let mut y : FloatArray := .emptyWithCapacity x.size
    for i in [0:x.size] do
      y := y.push (Float.exp (x.uget i.toUSize sorry_proof))
    y

  log x := Id.run do
    let mut y : FloatArray := .emptyWithCapacity x.size
    for i in [0:x.size] do
      y := y.push (Float.log (x.uget i.toUSize sorry_proof))
    y

  softmax x := Id.run do
    -- Find max for numerical stability
    let mut m := x.uget 0 sorry_proof
    for i in [1:x.size] do
      let v := x.uget i.toUSize sorry_proof
      if v > m then m := v
    -- Compute exp(x - max) and sum
    let mut expx : FloatArray := .emptyWithCapacity x.size
    let mut s := 0.0
    for i in [0:x.size] do
      let e := Float.exp (x.uget i.toUSize sorry_proof - m)
      expx := expx.push e
      s := s + e
    -- Normalize
    let mut y : FloatArray := .emptyWithCapacity x.size
    for i in [0:x.size] do
      y := y.push (expx.uget i.toUSize sorry_proof / s)
    y

/-! ## Metal Backend (when available) -/

-- Metal backend is defined in SciLean.FFI.Metal
-- Here we provide the typeclass instance that uses it

/-! ## Backend Selection -/

/-- Get the best available backend device -/
def Device.best : IO Device := do
  -- TODO: Check Metal availability via FFI
  -- For now, default to CPU
  return .cpu

/-- Run computation on a specific device -/
def withDevice {B : Type} (_d : Device) [TensorBackend B] (f : B → B) (x : B) : B :=
  f x

end SciLean
