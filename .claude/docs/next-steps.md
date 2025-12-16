# Next Steps for GPU Backend

## Completed ✓

- [x] Phase 1: Core tensor types (Device, CpuTensor, GpuTensor, GpuBufferN)
- [x] Phase 2: TensorOps/TensorOpsIO typeclasses
- [x] Phase 3: Command buffer batching in Metal backend
- [x] Phase 4: GPU monad
- [x] Phase 5: Basic autodiff gradient functions
- [x] Tests in `test/tensor_basic.lean`

## Priority Tasks

### 1. Full Autodiff Integration (High Priority)

The gradient functions exist but aren't integrated with SciLean's `@[fun_trans]` system.

**What's needed:**
```lean
-- In SciLean/AD/TensorRevFDeriv.lean, add proper instances:

instance : NormedAddCommGroup (CpuTensor Float ι) where
  -- Need to implement norm, dist, etc.

instance : AdjointSpace Float (CpuTensor Float ι) where
  -- Need inner product implementation

-- Then add @[fun_trans] theorems:
@[fun_trans]
theorem CpuTensor.add.revFDeriv_rule :
    revFDeriv Float (fun (ab : CpuTensor Float ι × CpuTensor Float ι) => ab.1 + ab.2)
    = fun ab => (ab.1 + ab.2, fun dt => (dt, dt)) := by
  unfold revFDeriv; sorry_proof
```

**Challenge:** Float doesn't satisfy mathematical axioms exactly. Use `sorry_proof` liberally.

### 2. Kernel Fusion (Medium Priority)

Add fused kernels to `Metal/kmeans.metal`:
- `gemm_bias_relu` - GEMM + bias + ReLU in one kernel
- `attention_fused` - Scaled dot-product attention
- `layer_norm` - Layer normalization

Then expose in `SciLean/FFI/Metal.lean` and `SciLean/Data/Tensor/Ops.lean`.

### 3. More GPU Operations (Medium Priority)

Add batching support to remaining ops in `metal_backend.mm`:
- `conv2d` variants
- `maxpool2d`, `avgpool2d`
- `batchnorm2d`

Pattern:
```objc
bool batched = is_batch_mode();
id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];
// ... dispatch ...
if (!batched) {
    [encoder endEncoding];
    [commandBuffer commit];
    [commandBuffer waitUntilCompleted];
}
```

### 4. High-Level ML API (Lower Priority)

Create `SciLean/Data/Tensor/ML.lean` with:
```lean
-- Layer abstractions
structure Dense (inDim outDim : Nat) where
  weights : GpuTensor Float (Idx outDim, Idx inDim)
  bias : GpuTensor Float (Idx outDim)

def Dense.forward (layer : Dense m n) (x : GpuTensor Float (Idx n)) : GPU (GpuTensor Float (Idx m)) := do
  let wx ← GPU.gemm layer.weights x
  let wxb ← GPU.add wx layer.bias
  GPU.relu wxb

-- Automatic device selection
def withBestDevice (f : GPU α) : IO α := do
  if Metal.isAvailable () then
    GPU.exec f
  else
    -- CPU fallback
    ...
```

## Testing Tasks

1. Add property-based tests with Plausible for tensor operations
2. Add GPU-specific tests (require Metal hardware)
3. Benchmark batched vs unbatched performance

## Documentation Tasks

1. Add module-level docstrings to tensor files
2. Create examples in `examples/` showing GPU usage
3. Add to main SciLean docs

## Build System Tasks

1. Make Metal backend optional (for non-macOS builds)
2. Add CI for tensor module
3. Consider CUDA backend structure

## How to Verify Your Changes

```bash
# Build specific modules
lake build SciLean.Data.Tensor
lake build SciLean.Monad.GPU
lake build SciLean.AD.TensorRevFDeriv

# Run tests
lake test

# Build everything
lake build
```

## Files to Read First

1. `SciLean/Data/Tensor/Basic.lean` - Core types
2. `SciLean/Monad/GPU.lean` - GPU monad
3. `Metal/metal_backend.mm` - Native backend (search for `is_batch_mode`)
4. `SciLean/FFI/Metal.lean` - FFI bindings
