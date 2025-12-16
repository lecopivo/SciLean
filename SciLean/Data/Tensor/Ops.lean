/-
Copyright (c) 2024 SciLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SciLean contributors
-/
import SciLean.Data.Tensor.Basic
import SciLean.Data.Tensor.Transfer

namespace SciLean

/-!
# Device-Polymorphic Tensor Operations

`TensorOps` is a typeclass providing device-polymorphic tensor operations.
Different instances handle CPU (BLAS) and GPU (Metal) implementations transparently.

The operations are defined for Float tensors as this is the common case for ML.
-/

variable {ι : Type*} {n : ℕ} [IndexType ι n]
variable {κ : Type*} {m : ℕ} [IndexType κ m]

/-! ## CPU Operations -/

namespace CpuTensor

/-- Element-wise addition -/
def add (a b : CpuTensor Float ι) : CpuTensor Float ι :=
  ⟨⊞ i => a.data[i] + b.data[i]⟩

/-- Element-wise multiplication -/
def mul (a b : CpuTensor Float ι) : CpuTensor Float ι :=
  ⟨⊞ i => a.data[i] * b.data[i]⟩

/-- Element-wise negation -/
def neg (a : CpuTensor Float ι) : CpuTensor Float ι :=
  ⟨⊞ i => -a.data[i]⟩

/-- Scalar multiplication -/
def smul (s : Float) (a : CpuTensor Float ι) : CpuTensor Float ι :=
  ⟨⊞ i => s * a.data[i]⟩

/-- ReLU activation: max(0, x) -/
def relu (a : CpuTensor Float ι) : CpuTensor Float ι :=
  ⟨⊞ i => if a.data[i] > 0 then a.data[i] else 0⟩

end CpuTensor

/-! ## GPU Operations (1D tensors) -/

namespace GpuTensor

/-- Element-wise addition on GPU -/
def add (a b : GpuTensor Float (Idx n)) : IO (GpuTensor Float (Idx n)) := do
  let result ← Metal.GpuBuffer.add a.data.buffer b.data.buffer n.toUSize
  return ⟨⟨result⟩⟩

/-- Element-wise multiplication on GPU -/
def mul (a b : GpuTensor Float (Idx n)) : IO (GpuTensor Float (Idx n)) := do
  let result ← Metal.GpuBuffer.mul a.data.buffer b.data.buffer n.toUSize
  return ⟨⟨result⟩⟩

/-- ReLU activation on GPU -/
def relu (a : GpuTensor Float (Idx n)) : IO (GpuTensor Float (Idx n)) := do
  let result ← Metal.GpuBuffer.relu a.data.buffer n.toUSize
  return ⟨⟨result⟩⟩

/-- Fused GEMM + Bias + ReLU: C = max(0, A @ B + bias)
    A: [m, k], B: [k, n], bias: [n], returns C: [m, n] -/
def gemmBiasRelu (A : GpuTensor Float (Idx m × Idx k)) (B : GpuTensor Float (Idx k × Idx n))
    (bias : GpuTensor Float (Idx n)) : IO (GpuTensor Float (Idx m × Idx n)) := do
  let result ← Metal.GpuBuffer.gemmBiasRelu A.data.buffer B.data.buffer bias.data.buffer
    m.toUSize k.toUSize n.toUSize
  return ⟨⟨result⟩⟩

end GpuTensor

/-! ## TensorOps Typeclass -/

/-- Type class for tensor operations that work across devices.
    For GPU operations, results are wrapped in IO. -/
class TensorOps (T : Type) where
  /-- Element-wise addition -/
  add : T → T → T
  /-- Element-wise multiplication (Hadamard product) -/
  mul : T → T → T
  /-- Scalar multiplication -/
  smul : Float → T → T

/-- CPU tensor operations (pure, no IO) -/
instance : TensorOps (CpuTensor Float ι) where
  add := CpuTensor.add
  mul := CpuTensor.mul
  smul := CpuTensor.smul

/-! ## TensorOpsIO for GPU -/

/-- Type class for tensor operations that may require IO (GPU) -/
class TensorOpsIO (T : Type) where
  /-- Element-wise addition -/
  add : T → T → IO T
  /-- Element-wise multiplication -/
  mul : T → T → IO T
  /-- ReLU activation -/
  relu : T → IO T

/-- GPU tensor operations (require IO) -/
instance : TensorOpsIO (GpuTensor Float (Idx n)) where
  add := GpuTensor.add
  mul := GpuTensor.mul
  relu := GpuTensor.relu

/-- Lift pure CPU ops to IO for uniform interface -/
instance [TensorOps T] : TensorOpsIO T where
  add a b := pure (TensorOps.add a b)
  mul a b := pure (TensorOps.mul a b)
  relu _ := panic! "relu not implemented for this tensor type"

/-! ## Algebra Instances for CPU Tensors -/

instance : Add (CpuTensor Float ι) where
  add := CpuTensor.add

instance : Neg (CpuTensor Float ι) where
  neg := CpuTensor.neg

instance : Sub (CpuTensor Float ι) where
  sub a b := CpuTensor.add a (CpuTensor.neg b)

instance : HMul Float (CpuTensor Float ι) (CpuTensor Float ι) where
  hMul := CpuTensor.smul

end SciLean
