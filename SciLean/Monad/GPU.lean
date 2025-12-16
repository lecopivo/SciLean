/-
Copyright (c) 2024 SciLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SciLean contributors
-/
import SciLean.Data.Tensor
import SciLean.FFI.Metal

namespace SciLean

/-!
# GPU Computation Monad

The GPU monad provides a structured way to sequence GPU operations with:
1. Automatic command buffer batching for performance
2. Type-safe device transfers
3. Clean composition of GPU computations

## Design Rationale

The GPU monad wraps IO but adds semantic meaning: operations within
a GPU computation block should be batched for efficiency. The `run`
function handles command buffer lifecycle automatically.

## Usage

```lean
-- Simple GPU computation
let result ← GPU.run do
  let a ← GPU.alloc (Float^[1024])
  let b ← GPU.alloc (Float^[1024])
  GPU.add a b

-- Compute with automatic CPU↔GPU transfers
let cpuResult ← GPU.compute cpuInput fun gpuTensor => do
  let temp ← GPU.relu gpuTensor
  GPU.add temp temp
```
-/

variable {ι : Type} {n : ℕ} [IndexType ι n]
variable {κ : Type} {m : ℕ} [IndexType κ m]

/-- The GPU monad for sequencing GPU operations.
    Wraps IO but provides semantic batching context. -/
structure GPU (α : Type) where
  /-- Run the GPU computation as an IO action -/
  run : IO α

namespace GPU

/-! ## Monad Instances -/

instance : Monad GPU where
  pure a := ⟨pure a⟩
  bind ma f := ⟨do let a ← ma.run; (f a).run⟩

instance : MonadLift IO GPU where
  monadLift io := ⟨io⟩

instance : Functor GPU where
  map f ma := ⟨Functor.map f ma.run⟩

instance : Applicative GPU where
  pure a := ⟨pure a⟩
  seq mf ma := ⟨do let f ← mf.run; let a ← (ma ()).run; pure (f a)⟩

/-! ## Core Operations -/

/-- Execute a GPU computation, handling command buffer batching.
    This is the primary entry point for running GPU code. -/
def exec (comp : GPU α) : IO α := do
  Metal.batchBegin
  try
    let result ← comp.run
    Metal.batchExecute
    return result
  catch e =>
    Metal.batchCancel
    throw e

/-- Execute a GPU computation with explicit error handling. -/
def tryExec (comp : GPU α) : IO (Except IO.Error α) := do
  try
    let result ← exec comp
    return .ok result
  catch e =>
    return .error e

/-! ## Tensor Operations in GPU Monad -/

/-- Allocate a GPU tensor. -/
def alloc {α : Type} [PlainDataType α] {ι : Type} {n : ℕ} [IndexType ι n]
    : GPU (GpuTensor α ι) :=
  ⟨GpuBufferN.alloc >>= (pure ⟨·⟩)⟩

/-- Transfer a CPU tensor to GPU. -/
def upload {α : Type} [PlainDataType α] {ι : Type} {n : ℕ} [IndexType ι n]
    (cpu : CpuTensor α ι) : GPU (GpuTensor α ι) :=
  ⟨cpu.toGpu⟩

/-- Transfer a GPU tensor to CPU. -/
def download {α : Type} [PlainDataType α] {ι : Type} {n : ℕ} [IndexType ι n]
    (gpu : GpuTensor α ι) : GPU (CpuTensor α ι) :=
  ⟨gpu.toCpu⟩

/-! ## GPU Tensor Operations -/

/-- Element-wise addition on GPU -/
def add (a b : GpuTensor Float (Idx n)) : GPU (GpuTensor Float (Idx n)) :=
  ⟨GpuTensor.add a b⟩

/-- Element-wise multiplication on GPU -/
def mul (a b : GpuTensor Float (Idx n)) : GPU (GpuTensor Float (Idx n)) :=
  ⟨GpuTensor.mul a b⟩

/-- ReLU activation on GPU -/
def relu (a : GpuTensor Float (Idx n)) : GPU (GpuTensor Float (Idx n)) :=
  ⟨GpuTensor.relu a⟩

/-- Fused GEMM + Bias + ReLU: C = max(0, A @ B + bias)
    More efficient than separate gemm → add → relu operations. -/
def gemmBiasRelu (A : GpuTensor Float (Idx m × Idx k)) (B : GpuTensor Float (Idx k × Idx n))
    (bias : GpuTensor Float (Idx n)) : GPU (GpuTensor Float (Idx m × Idx n)) :=
  ⟨GpuTensor.gemmBiasRelu A B bias⟩

/-! ## High-Level Compute Patterns -/

/-- Run a GPU computation on a CPU tensor with automatic transfers.
    This is the most convenient way to use GPU acceleration:
    1. Uploads input to GPU
    2. Runs the computation
    3. Downloads result back to CPU

    All within a single batched command buffer. -/
def compute [PlainDataType α] (input : CpuTensor α ι)
    (f : GpuTensor α ι → GPU (GpuTensor α ι)) : IO (CpuTensor α ι) := do
  exec do
    let gpuIn ← upload input
    let gpuOut ← f gpuIn
    download gpuOut

/-- Run a GPU computation on multiple CPU tensors. -/
def compute2 [PlainDataType α] (in1 : CpuTensor α ι) (in2 : CpuTensor α ι)
    (f : GpuTensor α ι → GpuTensor α ι → GPU (GpuTensor α ι))
    : IO (CpuTensor α ι) := do
  exec do
    let gpu1 ← upload in1
    let gpu2 ← upload in2
    let result ← f gpu1 gpu2
    download result

/-- Map a GPU operation over a CPU tensor. -/
def map [PlainDataType α] (f : GpuTensor α ι → GPU (GpuTensor α ι))
    (cpu : CpuTensor α ι) : IO (CpuTensor α ι) :=
  compute cpu f

/-- Fold over GPU tensors, keeping intermediate results on GPU. -/
def foldGpu [PlainDataType α] [Inhabited (GpuTensor α ι)]
    (f : GpuTensor α ι → GpuTensor α ι → GPU (GpuTensor α ι))
    (init : GpuTensor α ι)
    (tensors : List (GpuTensor α ι)) : GPU (GpuTensor α ι) := do
  let mut acc := init
  for t in tensors do
    acc ← f acc t
  return acc

end GPU

/-! ## Convenience Aliases -/

/-- Run a GPU computation with automatic batching. -/
abbrev runGpu := @GPU.exec

end SciLean
