/-
Copyright (c) 2024 SciLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SciLean contributors
-/
import SciLean.FFI.Metal
import SciLean.Data.IndexType.Basic
import SciLean.Data.DataArray.PlainDataType
import SciLean.Data.DataArray.DataArray

namespace SciLean

/-!
# Shape-tracked GPU Buffer

`GpuBufferN α ι` is a GPU-resident buffer with element type `α` and shape tracked by index type `ι`.
This mirrors `DataArrayN α ι` but lives on GPU (Metal) rather than CPU.

The shape is encoded in the type via `IndexType ι n`, guaranteeing the buffer has exactly `n` elements
at compile time. The underlying `GpuBuffer` is opaque, so size invariants are maintained by
construction rather than stored proofs.
-/

/-- GPU buffer with shape tracked in the type.
    Mirrors `DataArrayN α ι` but data lives on GPU (Metal).

    Unlike DataArrayN, we don't carry a size proof because GpuBuffer is opaque.
    Instead, the size invariant is maintained by construction. -/
structure GpuBufferN (α : Type*) [PlainDataType α] (ι : Type*) {n : outParam ℕ} [IndexType ι n] : Type where
  /-- The underlying GPU buffer handle -/
  buffer : Metal.GpuBuffer

namespace GpuBufferN

variable {α : Type*} [pd : PlainDataType α]
variable {ι : Type*} {n : ℕ} [IndexType ι n]

/-- Create a GPU buffer from a DataArrayN (CPU → GPU transfer) -/
def fromDataArrayN (arr : DataArrayN α ι) : IO (GpuBufferN α ι) := do
  let gpuBuf ← Metal.GpuBuffer.fromByteArray arr.data.byteData
  return ⟨gpuBuf⟩

/-- Copy GPU buffer back to CPU as DataArrayN (GPU → CPU transfer) -/
def toDataArrayN (buf : GpuBufferN α ι) : IO (DataArrayN α ι) := do
  let bytes ← Metal.GpuBuffer.toByteArray buf.buffer
  let data : DataArray α := ⟨bytes, sorry_proof⟩
  return ⟨data, sorry_proof⟩

/-- Allocate uninitialized GPU buffer of given shape -/
def alloc : IO (GpuBufferN α ι) := do
  let elemBytes := pd.btype.bytes
  let gpuBuf ← Metal.GpuBuffer.alloc (n.toUSize * elemBytes)
  return ⟨gpuBuf⟩

/-- Number of elements in the buffer (known at compile time from type) -/
def size (_ : GpuBufferN α ι) : ℕ := n

/-- Size as USize for FFI calls -/
def usize (_ : GpuBufferN α ι) : USize := n.toUSize

/-- Get underlying buffer size in bytes (runtime check) -/
def sizeBytes (buf : GpuBufferN α ι) : USize :=
  Metal.GpuBuffer.sizeBytes buf.buffer

end GpuBufferN

/-- Notation for GPU buffer types, matching DataArrayN notation -/
scoped notation:max α "^[" ι "]ᵍ" => GpuBufferN α ι

end SciLean
