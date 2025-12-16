/-
Copyright (c) 2024 SciLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SciLean contributors
-/
import SciLean.Data.Tensor.Basic

namespace SciLean

/-!
# Device Transfer Operations

Type-safe transfers between CPU and GPU tensors. The device is tracked in the type,
so transfers are explicit and visible in function signatures.

Example:
```lean
def forward (weights : GpuTensor Float (Idx 128, Idx 784)) (input : CpuTensor Float (Idx 784)) : IO (CpuTensor Float (Idx 128)) := do
  let gpuInput ← input.toGpu
  let output ← TensorOps.gemm weights gpuInput  -- GPU computation
  output.toCpu
```
-/

variable {α : Type*} [PlainDataType α]
variable {ι : Type*} {n : ℕ} [IndexType ι n]

/-! ## CPU → GPU Transfer -/

/-- Transfer CPU tensor to GPU -/
def CpuTensor.toGpu (t : CpuTensor α ι) : IO (GpuTensor α ι) := do
  let gpuBuf ← GpuBufferN.fromDataArrayN t.data
  return ⟨gpuBuf⟩

/-! ## GPU → CPU Transfer -/

/-- Transfer GPU tensor to CPU -/
def GpuTensor.toCpu (t : GpuTensor α ι) : IO (CpuTensor α ι) := do
  let cpuArr ← GpuBufferN.toDataArrayN t.data
  return ⟨cpuArr⟩

/-! ## Polymorphic Transfer API -/

/-- Transfer a tensor to GPU. Identity for GPU tensors, copy for CPU tensors. -/
class ToGpu (T : Type) (G : outParam Type) where
  toGpu : T → IO G

instance : ToGpu (CpuTensor α ι) (GpuTensor α ι) where
  toGpu := CpuTensor.toGpu

instance : ToGpu (GpuTensor α ι) (GpuTensor α ι) where
  toGpu t := pure t

/-- Transfer a tensor to CPU. Identity for CPU tensors, copy for GPU tensors. -/
class ToCpu (T : Type) (C : outParam Type) where
  toCpu : T → IO C

instance : ToCpu (GpuTensor α ι) (CpuTensor α ι) where
  toCpu := GpuTensor.toCpu

instance : ToCpu (CpuTensor α ι) (CpuTensor α ι) where
  toCpu t := pure t

/-! ## Convenience Functions -/

/-- Run a GPU computation on CPU data, handling transfers automatically -/
def withGpu (input : CpuTensor α ι)
    (f : GpuTensor α ι → IO (GpuTensor α ι))
    : IO (CpuTensor α ι) := do
  let gpuIn ← input.toGpu
  let gpuOut ← f gpuIn
  gpuOut.toCpu

/-- Run a GPU computation on CPU data with different output shape -/
def withGpu' {β : Type*} [PlainDataType β] {κ : Type*} {m : ℕ} [IndexType κ m]
    (input : CpuTensor α ι)
    (f : GpuTensor α ι → IO (GpuTensor β κ))
    : IO (CpuTensor β κ) := do
  let gpuIn ← input.toGpu
  let gpuOut ← f gpuIn
  gpuOut.toCpu

/-- Transfer DataArrayN directly to GPU -/
def DataArrayN.toGpu (arr : DataArrayN α ι) : IO (GpuTensor α ι) :=
  CpuTensor.toGpu ⟨arr⟩

/-- Alias for compatibility with Tensor notation -/
abbrev Tensor.toGpu [ToGpu T G] (t : T) : IO G := ToGpu.toGpu t
abbrev Tensor.toCpu [ToCpu T C] (t : T) : IO C := ToCpu.toCpu t

end SciLean
