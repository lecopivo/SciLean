/-
Copyright (c) 2024 SciLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SciLean contributors
-/
import SciLean.Data.Tensor

open SciLean

/-!
# Tensor Type Tests

Compilation-only tests for the device-tracked Tensor types.
These tests verify that types elaborate correctly and basic operations type-check.
On macOS, `#eval` is disabled due to precompilation constraints.
-/

/-! ## Type Elaboration Tests -/

-- Device type
#check Device.cpu
#check Device.metal
#check (Device.cpu : Device)

-- CpuTensor construction and coercion
#check (⟨⊞[1.0, 2.0, 3.0]⟩ : CpuTensor Float (Idx 3))
#check CpuTensor.ofDataArrayN (⊞[1.0, 2.0, 3.0] : Float^[Idx 3])

-- GpuTensor type (no construction - requires Metal)
#check GpuTensor Float (Idx 3)
#check GpuBufferN Float (Idx 3)

-- Tensor type abbreviation
#check Tensor Device.cpu Float (Idx 3)
#check Tensor Device.metal Float (Idx 3)

/-! ## Operation Type Checking -/

-- CpuTensor operations
variable (a b : CpuTensor Float (Idx 3))

#check CpuTensor.add a b
#check CpuTensor.mul a b
#check CpuTensor.neg a
#check CpuTensor.smul 2.0 a
#check CpuTensor.relu a

-- Algebra instances
#check a + b
#check -a
#check a - b
#check (2.0 : Float) * a

-- TensorOps typeclass
#check TensorOps.add a b
#check TensorOps.mul a b
#check TensorOps.smul 2.0 a

-- TensorOpsIO (pure lift for CPU)
#check (TensorOpsIO.add a b : IO _)
#check (TensorOpsIO.mul a b : IO _)

/-! ## Transfer Operations Type Checking -/

-- CPU to GPU transfer
#check CpuTensor.toGpu (a : CpuTensor Float (Idx 3))

-- GPU to CPU transfer
variable (g : GpuTensor Float (Idx 3))
#check GpuTensor.toCpu g

-- ToGpu/ToCpu typeclasses
#check (ToGpu.toGpu a : IO _)
#check (ToCpu.toCpu g : IO _)

-- withGpu helper
#check withGpu a (fun (g : GpuTensor Float (Idx 3)) => do return g)

/-! ## GetElem Instance Tests -/

-- Element access for CpuTensor
#check (a[(0 : Idx 3)] : Float)

/-! ## Property Tests (compile-time verification) -/

-- Helper to create CpuTensor from list
def mkTensor3 (x y z : Float) : CpuTensor Float (Idx 3) :=
  CpuTensor.ofDataArrayN ⊞[x, y, z]

-- These proofs verify properties at compile time via native_decide
-- Commutativity of addition
example : let a := mkTensor3 1.0 2.0 3.0
          let b := mkTensor3 4.0 5.0 6.0
          (a + b).toDataArrayN = (b + a).toDataArrayN := by native_decide

-- Associativity of addition
example : let a := mkTensor3 1.0 2.0 3.0
          let b := mkTensor3 4.0 5.0 6.0
          let c := mkTensor3 7.0 8.0 9.0
          ((a + b) + c).toDataArrayN = (a + (b + c)).toDataArrayN := by native_decide

-- Identity: a + 0 = a
example : let a := mkTensor3 1.0 2.0 3.0
          let zero := mkTensor3 0.0 0.0 0.0
          (a + zero).toDataArrayN = a.toDataArrayN := by native_decide

-- Negation: a + (-a) = 0
example : let a := mkTensor3 1.0 2.0 3.0
          let zero := mkTensor3 0.0 0.0 0.0
          (a + (-a)).toDataArrayN = zero.toDataArrayN := by native_decide

-- Scalar multiplication distributes over addition
example : let a := mkTensor3 1.0 2.0 3.0
          let b := mkTensor3 4.0 5.0 6.0
          let s : Float := 2.0
          (s * (a + b)).toDataArrayN = (s * a + s * b).toDataArrayN := by native_decide
