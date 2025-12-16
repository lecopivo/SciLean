# Tensor Module Quick Start

## What Exists

Device-tracked tensor types with Metal GPU acceleration:

```lean
import SciLean.Data.Tensor
import SciLean.Monad.GPU

-- CPU tensor (wraps DataArrayN)
def cpu : CpuTensor Float (Idx 100) := ⟨⊞ i => i.1.toFloat⟩

-- GPU computation with batching
def gpuCompute (input : CpuTensor Float (Idx 100)) : IO (CpuTensor Float (Idx 100)) :=
  GPU.exec do
    let gpu ← GPU.upload input
    let result ← GPU.relu gpu
    GPU.download result
```

## File Layout

```
SciLean/
├── Data/Tensor/
│   ├── Basic.lean      -- Device, CpuTensor, GpuTensor
│   ├── GpuBufferN.lean -- Shape-tracked GPU buffer
│   ├── Transfer.lean   -- toGpu/toCpu
│   └── Ops.lean        -- TensorOps, TensorOpsIO
├── Monad/
│   └── GPU.lean        -- GPU monad with batching
├── AD/
│   └── TensorRevFDeriv.lean -- Gradient functions
└── FFI/
    └── Metal.lean      -- Metal FFI bindings

Metal/
└── metal_backend.mm    -- C++/ObjC Metal backend

test/
├── Smoke.lean          -- Test entry point
└── tensor_basic.lean   -- Tensor tests
```

## Key Types

| Type | Description |
|------|-------------|
| `Device` | `.cpu` or `.metal` |
| `CpuTensor α ι` | CPU tensor with element type `α`, shape `ι` |
| `GpuTensor α ι` | GPU tensor (Metal) |
| `GpuBufferN α ι` | Shape-tracked GPU buffer |
| `GPU α` | GPU computation monad |

## Key Functions

| Function | Description |
|----------|-------------|
| `GPU.exec` | Run GPU computation with batching |
| `GPU.upload` | CPU → GPU transfer |
| `GPU.download` | GPU → CPU transfer |
| `GPU.add/mul/relu` | GPU tensor operations |
| `GPU.compute` | Upload → compute → download |
| `Metal.withBatch` | Lower-level batching API |

## Gradient Functions

```lean
gradAdd, gradMul, gradNeg, gradSmul, gradSub, gradRelu
CpuTensor.reluGrad  -- ReLU subgradient
backwardDense       -- Example backward pass
```

## Build & Test

```bash
lake build SciLean.Data.Tensor
lake build SciLean.Monad.GPU
lake test
```

## What's Missing / Future Work

1. **Full autodiff integration** - Need typeclass instances for `@[fun_trans]`
2. **Kernel fusion** - Fused ops like `gemm_bias_relu`
3. **More GPU ops** - conv2d batching, etc.
4. **CUDA backend** - Currently Metal-only

## Common Issues

- **Test conflicts**: Test library is `SciLeanTest` not `Test` (conflicts with SorryProof)
- **Metal linking**: Executables need `moreLinkArgs := metalLinkArgs` in lakefile
- **sorry_proof usage**: Expected in this repo - verification isn't the priority
