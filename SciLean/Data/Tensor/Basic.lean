/-
Copyright (c) 2024 SciLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SciLean contributors
-/
import SciLean.Data.DataArray
import SciLean.Data.Tensor.GpuBufferN

namespace SciLean

/-!
# Device-Tracked Tensor Type

`Tensor d α ι` is a tensor with element type `α` and shape tracked by index type `ι`,
where `d : Device` specifies whether data resides on CPU or GPU (Metal).

The device is encoded in the type, providing compile-time guarantees about data location
and eliminating runtime dispatch overhead. This enables:
- Type-safe transfers between devices (`toGpu`, `toCpu`)
- Device-specific optimizations in TensorOps typeclass instances
- Zero-cost abstraction over DataArrayN for CPU tensors
-/

/-- Compute device for tensor operations -/
inductive Device where
  | cpu    -- CPU with DataArrayN storage
  | metal  -- GPU via Metal with GpuBufferN storage
  deriving DecidableEq, Repr, Inhabited

namespace Device

/-- Check if Metal GPU is available at runtime -/
def metalAvailable : IO Bool := do
  -- TODO: Add actual Metal availability check via FFI
  return true

/-- Get best available device (prefers GPU) -/
def best : IO Device := do
  if ← metalAvailable then
    return .metal
  else
    return .cpu

instance : ToString Device where
  toString
    | .cpu => "cpu"
    | .metal => "metal"

end Device

/-- CPU Tensor - wraps DataArrayN with device tracking -/
structure CpuTensor (α : Type*) [PlainDataType α] (ι : Type*) {n : outParam ℕ} [IndexType ι n] : Type where
  /-- The underlying CPU array -/
  data : DataArrayN α ι

/-- GPU Tensor - wraps GpuBufferN with device tracking -/
structure GpuTensor (α : Type*) [PlainDataType α] (ι : Type*) {n : outParam ℕ} [IndexType ι n] : Type where
  /-- The underlying GPU buffer -/
  data : GpuBufferN α ι

/-- Device-indexed tensor type. Maps Device to appropriate storage type. -/
abbrev Tensor (d : Device) (α : Type*) [PlainDataType α] (ι : Type*) {n : outParam ℕ} [IndexType ι n] : Type :=
  match d with
  | .cpu => CpuTensor α ι
  | .metal => GpuTensor α ι

namespace CpuTensor

variable {α : Type*} [PlainDataType α]
variable {ι : Type*} {n : ℕ} [IndexType ι n]

/-! ## Construction -/

/-- Create from DataArrayN -/
@[inline]
def ofDataArrayN (arr : DataArrayN α ι) : CpuTensor α ι := ⟨arr⟩

/-- Extract DataArrayN -/
@[inline]
def toDataArrayN (t : CpuTensor α ι) : DataArrayN α ι := t.data

/-! ## Zero-Cost Coercions -/

instance : Coe (DataArrayN α ι) (CpuTensor α ι) where
  coe := ofDataArrayN

instance : Coe (CpuTensor α ι) (DataArrayN α ι) where
  coe := toDataArrayN

/-! ## Basic Properties -/

/-- Number of elements -/
def size (_ : CpuTensor α ι) : ℕ := n

/-- Size as USize -/
def usize (_ : CpuTensor α ι) : USize := n.toUSize

/-! ## Element Access -/

/-- Get element at index -/
@[inline]
def get (t : CpuTensor α ι) (i : ι) : α := t.data.get i

/-- Set element at index -/
@[inline]
def set (t : CpuTensor α ι) (i : ι) (v : α) : CpuTensor α ι :=
  ⟨t.data.set i v⟩

instance : GetElem (CpuTensor α ι) ι α (fun _ _ => True) where
  getElem t i _ := t.get i

instance : SetElem (CpuTensor α ι) ι α (fun _ _ => True) where
  setElem t i v _ := t.set i v
  setElem_valid := sorry_proof

end CpuTensor

namespace GpuTensor

variable {α : Type*} [PlainDataType α]
variable {ι : Type*} {n : ℕ} [IndexType ι n]

/-! ## Construction -/

/-- Create from GpuBufferN -/
@[inline]
def ofGpuBufferN (buf : GpuBufferN α ι) : GpuTensor α ι := ⟨buf⟩

/-- Extract GpuBufferN -/
@[inline]
def toGpuBufferN (t : GpuTensor α ι) : GpuBufferN α ι := t.data

/-! ## Zero-Cost Coercions -/

instance : Coe (GpuBufferN α ι) (GpuTensor α ι) where
  coe := ofGpuBufferN

instance : Coe (GpuTensor α ι) (GpuBufferN α ι) where
  coe := toGpuBufferN

/-! ## Basic Properties -/

/-- Number of elements -/
def size (_ : GpuTensor α ι) : ℕ := n

/-- Size as USize -/
def usize (_ : GpuTensor α ι) : USize := n.toUSize

end GpuTensor

/-! ## Notation -/

/-- Notation for tensor types: `α^[ι]@d` for Tensor d α ι -/
scoped notation:max α "^[" ι "]@cpu" => CpuTensor α ι
scoped notation:max α "^[" ι "]@metal" => GpuTensor α ι

end SciLean
