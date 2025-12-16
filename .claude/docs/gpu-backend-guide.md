# SciLean GPU Backend Architecture Guide

This guide documents the GPU backend architecture implemented for SciLean, enabling device-tracked tensors with Metal GPU acceleration.

## Architecture Overview

```
┌──────────────────────────────────────────────┐
│  SciLean Dependent Types + Autodiff          │
│  CpuTensor, GpuTensor, GPU monad             │
└──────────────────────────────────────────────┘
                     │
                     ▼
┌──────────────────────────────────────────────┐
│  Tensor Types (SciLean/Data/Tensor/)         │
│  Device enum, transfers, operations          │
└──────────────────────────────────────────────┘
                     │
                     ▼
┌──────────────────────────────────────────────┐
│  Metal FFI (SciLean/FFI/Metal.lean)          │
│  GpuBuffer, batching, GPU ops                │
└──────────────────────────────────────────────┘
                     │
                     ▼
┌──────────────────────────────────────────────┐
│  C++/ObjC Backend (Metal/metal_backend.mm)   │
│  Command buffers, compute pipelines          │
└──────────────────────────────────────────────┘
```

## Key Files

### Tensor Types (`SciLean/Data/Tensor/`)

- **Basic.lean**: `Device` enum (`.cpu`, `.metal`), `CpuTensor`, `GpuTensor` structures
- **GpuBufferN.lean**: Shape-tracked GPU buffer mirroring `DataArrayN`
- **Transfer.lean**: Type-safe `toGpu`/`toCpu` transfers with `ToGpu`/`ToCpu` typeclasses
- **Ops.lean**: `TensorOps` (pure CPU) and `TensorOpsIO` (GPU, requires IO) typeclasses

### GPU Monad (`SciLean/Monad/GPU.lean`)

The `GPU` monad sequences GPU operations with automatic command buffer batching:

```lean
-- Example usage
def forward (input : CpuTensor Float (Idx 784)) : IO (CpuTensor Float (Idx 128)) :=
  GPU.exec do
    let gpuIn ← GPU.upload input
    let result ← GPU.relu gpuIn
    GPU.download result
```

Key functions:
- `GPU.exec` - Run GPU computation with batching
- `GPU.upload` / `GPU.download` - CPU↔GPU transfers
- `GPU.add`, `GPU.mul`, `GPU.relu` - GPU tensor operations
- `GPU.compute` - High-level: upload → compute → download

### Autodiff (`SciLean/AD/TensorRevFDeriv.lean`)

Gradient computation functions for backpropagation:
- `gradAdd`, `gradMul`, `gradNeg`, `gradSmul`, `gradSub`, `gradRelu`
- `CpuTensor.reluGrad` - ReLU subgradient helper
- `backwardDense` - Example backward pass

Note: Full `@[fun_trans]` integration requires proper typeclass instances on CpuTensor (NormedAddCommGroup, AdjointSpace). Currently provides computational gradient functions.

### Metal Backend (`Metal/metal_backend.mm`)

C++/Objective-C Metal backend with:
- Buffer pooling for allocation efficiency
- Command buffer batching (3-5x speedup for op chains)
- GPU-resident buffers (`GpuBuffer` type)

**Batching API** (added in this work):
```objc
// Global state
static bool g_batch_mode = false;
static id<MTLCommandBuffer> g_batch_command_buffer = nil;
static id<MTLComputeCommandEncoder> g_batch_encoder = nil;

// FFI functions
scilean_gpu_batch_begin()   // Start batching
scilean_gpu_batch_execute() // Submit all queued ops
scilean_gpu_batch_cancel()  // Cancel without executing
```

Operations updated for batching: `gemm`, `add`, `mul`, `relu`, `softmax`

### Metal FFI (`SciLean/FFI/Metal.lean`)

Lean bindings for Metal:
- `Metal.GpuBuffer` - Opaque GPU buffer handle
- `Metal.withBatch` - Execute batched GPU computation
- `Metal.batchBegin`, `Metal.batchExecute`, `Metal.batchCancel`

## Testing

Tests are in `test/tensor_basic.lean`, imported by `test/Smoke.lean`.

**Important**: The test library is named `SciLeanTest` (not `Test`) to avoid conflict with SorryProof's Test library. Configuration is in `lakefile.lean`:

```lean
@[test_driver]
lean_lib SciLeanTest {
  srcDir := "test"
  roots := if System.Platform.isOSX then #[`Smoke] else #[]
  ...
}
```

Run tests: `lake test`

## Build Commands

```bash
# Build tensor module
lake build SciLean.Data.Tensor

# Build GPU monad
lake build SciLean.Monad.GPU

# Build autodiff
lake build SciLean.AD.TensorRevFDeriv

# Run tests
lake test
```

## Future Work

### Remaining from original plan:

1. **Phase 6: Kernel Fusion** - Add fused kernels (`gemm_bias_relu`, etc.) to `Metal/kmeans.metal`

2. **Phase 7: High-Level API** - Create `SciLean/Data/Tensor/ML.lean` with ML-focused convenience API

3. **Full `@[fun_trans]` integration** - Add proper typeclass instances for CpuTensor:
   - `NormedAddCommGroup (CpuTensor Float ι)`
   - `AdjointSpace Float (CpuTensor Float ι)`
   - Then add `@[fun_trans]` theorems for automatic differentiation

### Performance optimizations:

1. More operations with batching support (conv2d, etc.)
2. Async command buffer execution (don't wait immediately)
3. Double-buffering for streaming workloads

## Common Patterns

### Adding a new GPU operation

1. Add FFI in `Metal/metal_backend.mm`:
```objc
LEAN_EXPORT lean_obj_res scilean_gpu_newop_f32(...) {
    // Check batch mode
    bool batched = is_batch_mode();
    id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
    id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

    // ... setup and dispatch ...

    if (!batched) {
        [encoder endEncoding];
        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];
    }
    // ...
}
```

2. Add Lean binding in `SciLean/FFI/Metal.lean`:
```lean
@[extern "scilean_gpu_newop_f32"]
opaque newOp (args...) : IO GpuBuffer
```

3. Add to `GpuTensor` in `SciLean/Data/Tensor/Ops.lean`:
```lean
def newOp (a : GpuTensor Float (Idx n)) : IO (GpuTensor Float (Idx n)) := do
  let result ← Metal.GpuBuffer.newOp a.data.buffer n.toUSize
  return ⟨⟨result⟩⟩
```

4. Add to GPU monad in `SciLean/Monad/GPU.lean`:
```lean
def newOp (a : GpuTensor Float (Idx n)) : GPU (GpuTensor Float (Idx n)) :=
  ⟨GpuTensor.newOp a⟩
```

5. Add gradient in `SciLean/AD/TensorRevFDeriv.lean`:
```lean
def gradNewOp (a dt : CpuTensor Float ι) : CpuTensor Float ι := ...
```

### Device-aware code

```lean
-- Type tracks device
def forward (input : CpuTensor Float (Idx 784)) : IO (CpuTensor Float (Idx 10)) :=
  GPU.exec do
    let gpu ← GPU.upload input          -- CpuTensor → GpuTensor
    let h1 ← GPU.relu gpu               -- GpuTensor → GpuTensor
    let out ← GPU.download h1           -- GpuTensor → CpuTensor
    return out

-- Or use compute pattern
def forward' (input : CpuTensor Float (Idx 784)) : IO (CpuTensor Float (Idx 784)) :=
  GPU.compute input GPU.relu
```

## Debugging Tips

1. **Build errors in Metal backend**: Check `Metal/metal_backend.mm` compiles with `clang++ -c`

2. **FFI linkage issues**: Ensure `moreLinkArgs := metalLinkArgs` in lakefile for executables using Metal

3. **Test library conflicts**: If tests fail to find modules, check `srcDir` and module naming in lakefile

4. **GPU not available**: `Metal.isAvailable()` returns false if no Metal GPU present
