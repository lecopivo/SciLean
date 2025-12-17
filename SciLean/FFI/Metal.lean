/-
Metal GPU Backend

Low-level FFI bindings to Metal compute shaders for GPU acceleration.
These operate on raw FloatArrays for minimal dependencies.

Operations: unary (neg, exp, log, etc), binary (add, mul), reductions (sum, max),
matrix (gemv, gemm variants), fill, kmeans.

Performance on M4: gemmSimd ~10 TFLOP/s, gemmTiled ~6 TFLOP/s at 2048x2048.
-/

import SciLean.FFI.Float32Array
import SciLean.Util.Float

namespace SciLean.Metal

/-! ## Core -/

/-- Check if Metal GPU acceleration is available -/
@[extern "scilean_metal_available"]
opaque isAvailable : Unit → Bool

/-- Run computation on GPU if available, otherwise fallback to CPU -/
def withGPU [Inhabited α] (gpuFn cpuFn : Unit → α) : α :=
  if isAvailable () then gpuFn () else cpuFn ()

/-! ## GPU-Resident Buffers -/

/-! ## Command Buffer Batching

When performing multiple GPU operations, each op normally creates its own command buffer
and waits for completion. This adds 10-50μs overhead per operation.

Batching allows multiple operations to queue into a single command buffer:
```
Metal.withBatch do
  let h1 ← GpuBuffer.gemm A B m k n
  let h2 ← GpuBuffer.relu h1 n
  let h3 ← GpuBuffer.add h2 bias n
  return h3
```
All three operations execute in one GPU submission, eliminating per-op sync overhead.
-/

/-- Begin a batch of GPU operations. Subsequent ops queue into shared command buffer. -/
@[extern "scilean_gpu_batch_begin"]
opaque batchBegin : IO Unit

/-- Execute all batched GPU operations and wait for completion. -/
@[extern "scilean_gpu_batch_execute"]
opaque batchExecute : IO Unit

/-- Cancel batch mode without executing (for error recovery). -/
@[extern "scilean_gpu_batch_cancel"]
opaque batchCancel : IO Unit

/-- Check if currently in batch mode. -/
@[extern "scilean_gpu_is_batch_mode"]
opaque isBatchMode : Unit → Bool

/-- Execute a batch of GPU operations in a single command buffer submission.
    This eliminates per-operation synchronization overhead (3-5x speedup for op chains). -/
def withBatch (f : IO α) : IO α := do
  batchBegin
  try
    let result ← f
    batchExecute
    return result
  catch e =>
    batchCancel
    throw e

/-- Opaque handle to a GPU-resident Metal buffer.
    Data stays on GPU until explicitly downloaded. -/
opaque GpuBufferPointed : NonemptyType
def GpuBuffer : Type := GpuBufferPointed.type
instance : Nonempty GpuBuffer := GpuBufferPointed.property

namespace GpuBuffer

/-- Allocate an uninitialized GPU buffer of given size (in floats) -/
@[extern "scilean_gpu_alloc_f32"]
opaque alloc (numFloats : USize) : IO GpuBuffer

/-- Upload ByteArray (Float32 data) to GPU (low-level, prefer `CpuBuffer.upload` for type safety) -/
@[extern "scilean_gpu_upload_f32"]
opaque fromByteArray (data : @& ByteArray) : IO GpuBuffer

/-- Download GPU buffer to ByteArray (low-level, prefer `GpuBuffer.download` for type safety) -/
@[extern "scilean_gpu_download_f32"]
opaque toByteArray (buf : @& GpuBuffer) : IO ByteArray

/-- Get size of buffer in bytes -/
@[extern "scilean_gpu_size"]
opaque sizeBytes (buf : @& GpuBuffer) : USize

/-- Free GPU buffer (optional - will be freed on GC anyway) -/
@[extern "scilean_gpu_free"]
opaque free (buf : GpuBuffer) : IO Unit

/-- Slice a GPU buffer: returns new buffer with elements [offset, offset + count).
    This is a GPU-to-GPU copy (not a view) for safe memory management.
    Offset and count are in number of Float32 elements. -/
@[extern "scilean_gpu_slice_f32"]
opaque slice (src : @& GpuBuffer) (offsetFloats countFloats : USize) : IO GpuBuffer

/-! ### GPU-to-GPU Operations (no CPU copies!) -/

/-- Matrix multiply on GPU: C = A * B
    A is [m, k], B is [k, n], returns C [m, n]
    Both inputs and output stay on GPU -/
@[extern "scilean_gpu_gemm_f32"]
opaque gemm (A B : @& GpuBuffer) (m k n : USize) : IO GpuBuffer

/-- Element-wise add: C = A + B -/
@[extern "scilean_gpu_add_f32"]
opaque add (A B : @& GpuBuffer) (n : USize) : IO GpuBuffer

/-- Element-wise multiply: C = A * B -/
@[extern "scilean_gpu_mul_f32"]
opaque mul (A B : @& GpuBuffer) (n : USize) : IO GpuBuffer

/-- ReLU activation (in-place capable) -/
@[extern "scilean_gpu_relu_f32"]
opaque relu (x : @& GpuBuffer) (n : USize) : IO GpuBuffer

/-- Softmax along rows -/
@[extern "scilean_gpu_softmax_f32"]
opaque softmax (x : @& GpuBuffer) (numRows rowSize : USize) : IO GpuBuffer

/-- Conv2D on GPU-resident buffers
    Input: [batch, inChannels, height, width] in NCHW format
    Kernel: [outChannels, inChannels, kH, kW]
    Bias: [outChannels]
    Returns output on GPU -/
@[extern "scilean_gpu_conv2d_f32"]
opaque conv2d (input kernel bias : @& GpuBuffer)
    (batchSize inChannels outChannels : USize)
    (inHeight inWidth : USize)
    (kernelH kernelW : USize)
    (strideH strideW : USize)
    (padH padW : USize)
    (useRelu : UInt8) : IO GpuBuffer

/-- MaxPool2D on GPU-resident buffers -/
@[extern "scilean_gpu_maxpool2d_f32"]
opaque maxPool2d (input : @& GpuBuffer)
    (batchSize channels : USize)
    (inHeight inWidth : USize)
    (poolH poolW : USize)
    (strideH strideW : USize) : IO GpuBuffer

/-- Bias + ReLU fused operation: y = max(0, x + bias) -/
@[extern "scilean_gpu_bias_relu_f32"]
opaque biasRelu (x bias : @& GpuBuffer) (n stride : USize) : IO GpuBuffer

/-- Fused GEMM + Bias + ReLU: C = max(0, A @ B + bias)
    A is [m, k], B is [k, n], bias is [n], returns C [m, n]
    bias is broadcasted along rows.
    More efficient than separate gemm → bias → relu operations. -/
@[extern "scilean_gpu_gemm_bias_relu_f32"]
opaque gemmBiasRelu (A B bias : @& GpuBuffer) (m k n : USize) : IO GpuBuffer

/-- Layer normalization: y = gamma * (x - mean) / sqrt(var + eps) + beta
    x is [n] total elements, hiddenSize is the normalization dimension.
    Supports batching. -/
@[extern "scilean_gpu_layer_norm_f32"]
opaque layerNorm (x gamma beta : @& GpuBuffer) (n hiddenSize : USize) : IO GpuBuffer

/-- Bias + GELU fused operation: y = gelu(x + bias)
    x is [n] elements, bias has [stride] elements broadcasted.
    GELU ≈ 0.5*x*(1+tanh(sqrt(2/π)*(x+0.044715*x³)))
    Supports batching. -/
@[extern "scilean_gpu_bias_gelu_f32"]
opaque biasGelu (x bias : @& GpuBuffer) (n stride : USize) : IO GpuBuffer

/-- Bias + add (no activation): y = x + bias (broadcast)
    For output layer before softmax where we don't want activation.
    n = total elements, stride = bias size (broadcast across batch).
    Supports batching. -/
@[extern "scilean_gpu_bias_add_f32"]
opaque biasAdd (x bias : @& GpuBuffer) (n stride : USize) : IO GpuBuffer

/-- Average pooling 2D
    Supports batching. -/
@[extern "scilean_gpu_avgpool2d_f32"]
opaque avgpool2d (x : @& GpuBuffer) (batchSize channels inHeight inWidth : USize)
    (poolH poolW : USize) (strideH strideW : USize) : IO GpuBuffer

/-- Flash Attention: output = softmax(Q @ K^T / sqrt(head_dim)) @ V
    Q, K, V are [seq_len, head_dim] matrices.
    Supports batching. -/
@[extern "scilean_gpu_flash_attention_f32"]
opaque flashAttention (Q K V : @& GpuBuffer) (seqLen headDim : USize) : IO GpuBuffer

/-- Flash Attention with causal mask
    Position i can only attend to positions <= i (for autoregressive models).
    Q, K, V are [seq_len, head_dim] matrices.
    Supports batching. -/
@[extern "scilean_gpu_flash_attention_causal_f32"]
opaque flashAttentionCausal (Q K V : @& GpuBuffer) (seqLen headDim : USize) : IO GpuBuffer

/-- Batch normalization 2D (inference mode)
    Input: [batch, channels, height, width] in NCHW format
    gamma (scale), beta (bias), mean, var: [channels] each
    eps: small constant for numerical stability (typically 1e-5)
    applyRelu: if 1, applies ReLU after normalization (fused op)
    Returns normalized output on GPU.
    Supports batching. -/
@[extern "scilean_gpu_batchnorm2d_f32"]
opaque batchNorm2d (input gamma beta mean var : @& GpuBuffer)
    (batchSize channels height width : USize)
    (eps : Float) (applyRelu : USize) : IO GpuBuffer

/-! ### Backward Pass Operations (for autodiff) -/

/-- ReLU backward: grad_input = grad_output * (input > 0 ? 1 : 0)
    Supports batching. -/
@[extern "scilean_gpu_relu_backward_f32"]
opaque reluBackward (input gradOutput : @& GpuBuffer) (n : USize) : IO GpuBuffer

/-- Element-wise multiply backward
    For c = a * b: grad_a = grad_c * b, grad_b = grad_c * a
    Returns (grad_a, grad_b) pair.
    Supports batching. -/
@[extern "scilean_gpu_mul_backward_f32"]
opaque mulBackward (a b gradOutput : @& GpuBuffer) (n : USize) : IO (GpuBuffer × GpuBuffer)

/-- GELU backward using approximation derivative
    Supports batching. -/
@[extern "scilean_gpu_gelu_backward_f32"]
opaque geluBackward (input gradOutput : @& GpuBuffer) (n : USize) : IO GpuBuffer

/-- Softmax backward (batched)
    For y = softmax(x): grad_x = y * (grad_y - sum(grad_y * y))
    Takes the softmax output (not input) for efficiency.
    Supports batching. -/
@[extern "scilean_gpu_softmax_backward_f32"]
opaque softmaxBackward (softmaxOutput gradOutput : @& GpuBuffer)
    (numRows rowSize : USize) : IO GpuBuffer

/-! ### Additional Training Operations -/

/-- AXPY: result = alpha * x + y (for SGD updates)
    Supports batching. -/
@[extern "scilean_gpu_axpy_f32"]
opaque axpy (n : USize) (alpha : Float) (x y : @& GpuBuffer) : IO GpuBuffer

/-- Scale: result = alpha * x (scalar multiplication)
    Supports batching. -/
@[extern "scilean_gpu_scale_f32"]
opaque scale (n : USize) (alpha : Float) (x : @& GpuBuffer) : IO GpuBuffer

/-- Subtraction: result = x - y
    Supports batching. -/
@[extern "scilean_gpu_sub_f32"]
opaque sub (x y : @& GpuBuffer) (n : USize) : IO GpuBuffer

/-- GEMM with first matrix transposed: C = A^T @ B
    A is stored as [k, m], computes A^T[m, k] @ B[k, n] = C[m, n]
    Supports batching. -/
@[extern "scilean_gpu_gemm_tn_f32"]
opaque gemmTN (A B : @& GpuBuffer) (m k n : USize) : IO GpuBuffer

/-- GEMM with second matrix transposed: C = A @ B^T
    A is [m, k], B is stored as [n, k], computes A @ B^T[k, n] = C[m, n]
    Supports batching. -/
@[extern "scilean_gpu_gemm_nt_f32"]
opaque gemmNT (A B : @& GpuBuffer) (m k n : USize) : IO GpuBuffer

/-- Sum all elements in buffer
    Supports batching. -/
@[extern "scilean_gpu_sum_f32"]
opaque sum (x : @& GpuBuffer) (n : USize) : IO Float

/-- Column-wise sum: for matrix [rows, cols], sum over rows for each column.
    Returns buffer of size [cols] (one sum per column).
    Used for gradient accumulation: sum gradients over batch dimension.
    Supports batching. -/
@[extern "scilean_gpu_row_sum_f32"]
opaque colSum (x : @& GpuBuffer) (rows cols : USize) : IO GpuBuffer

end GpuBuffer

/-! ## Type-Safe CPU/GPU Buffer System

Data transfer between CPU and GPU is a major performance bottleneck. This type system
makes transfers **explicit** at the type level - no implicit coercions allowed!

- `CpuBuffer` - CPU-resident data (wrapper around ByteArray)
- `GpuBuffer` - GPU-resident data (opaque Metal buffer handle)

To transfer data, you MUST use explicit functions:
- `CpuBuffer.upload : CpuBuffer → IO GpuBuffer` (CPU → GPU)
- `GpuBuffer.download : GpuBuffer → IO CpuBuffer` (GPU → CPU)

This prevents accidental data transfers that kill performance. GPU operations only
accept `GpuBuffer`, CPU operations only accept `CpuBuffer`.

Usage pattern:
```lean
-- Load data on CPU
let cpuWeights : CpuBuffer := ⟨weightData⟩
let cpuInput : CpuBuffer := ⟨inputData⟩

-- Explicit upload to GPU
let gpuWeights ← cpuWeights.upload
let gpuInput ← cpuInput.upload

-- Chain operations on GPU (no copies! type system enforces this)
let h1 ← GpuBuffer.gemm gpuWeights gpuInput m k n
let h2 ← GpuBuffer.relu h1

-- Explicit download when needed
let cpuOutput ← h2.download
let outputBytes := cpuOutput.data  -- access underlying ByteArray
```
-/

/-- CPU-resident buffer. Wrapper around ByteArray that prevents implicit conversion to GpuBuffer.
    Use `.upload` to explicitly move data to GPU. -/
structure CpuBuffer where
  /-- The underlying raw byte data (Float32 format) -/
  data : ByteArray
  deriving Inhabited

namespace CpuBuffer

/-- Size in bytes -/
@[inline] def sizeBytes (buf : CpuBuffer) : Nat := buf.data.size

/-- Size in Float32 elements -/
@[inline] def numFloats (buf : CpuBuffer) : Nat := buf.data.size / 4

/-- Create a zero-initialized CPU buffer with n Float32 elements -/
def zeros (n : Nat) : CpuBuffer :=
  ⟨ByteArray.replicateFloat32 n 0.0⟩

/-- Upload CPU buffer to GPU. This is an EXPLICIT transfer operation. -/
def upload (buf : CpuBuffer) : IO GpuBuffer :=
  GpuBuffer.fromByteArray buf.data

end CpuBuffer

namespace GpuBuffer

/-- Download GPU buffer to CPU. This is an EXPLICIT transfer operation.
    Returns a type-safe CpuBuffer wrapper. -/
def download (buf : GpuBuffer) : IO CpuBuffer := do
  let data ← toByteArray buf
  return ⟨data⟩

end GpuBuffer

-- IMPORTANT: No `Coe CpuBuffer GpuBuffer` instance!
-- IMPORTANT: No `Coe CpuBuffer ByteArray` instance!
-- IMPORTANT: No `Coe ByteArray CpuBuffer` instance!
-- All transfers must be explicit.

/-! ## Matrix Operations -/

-- Matrix-vector multiply on GPU: y = A * x. A is m x n, x is n-dim, returns m-dim y
@[extern "scilean_metal_gemv"]
opaque gemv (m n : USize) (A x : @& FloatArray) : FloatArray

-- Matrix multiply on GPU: C = A * B. A is m x k, B is k x n, returns m x n matrix C
@[extern "scilean_metal_gemm"]
opaque gemm (m k n : USize) (A B : @& FloatArray) : FloatArray

-- Tiled matrix multiply on GPU: C = A * B (optimized with 32x32 shared memory tiles)
@[extern "scilean_metal_gemm_tiled"]
opaque gemmTiled (m k n : USize) (A B : @& FloatArray) : FloatArray

-- Simdgroup matrix multiply on GPU: C = A * B (uses Apple Silicon's hardware matrix units)
-- Each simdgroup (32 threads) computes 8×8 output tiles using simdgroup_float8x8
@[extern "scilean_metal_gemm_simd"]
opaque gemmSimd (m k n : USize) (A B : @& FloatArray) : FloatArray

-- Smart GEMM: selects best kernel based on matrix size
-- - < 128×128: naive (low overhead)
-- - 128-512: tiled (good cache reuse)
-- - > 512: simd (hardware matrix units)
-- NOTE: Using native USize arithmetic to avoid BigNat allocation
@[inline] def gemmAuto (m k n : USize) (A B : @& FloatArray) : FloatArray :=
  let size := m * n  -- USize multiplication
  if size >= (512 : USize) * 512 then
    gemmSimd m k n A B
  else if size >= (128 : USize) * 128 then
    gemmTiled m k n A B
  else
    gemm m k n A B

/-! ## Unary Operations -/

/-- Element-wise negation -/
@[extern "scilean_metal_neg"]
opaque neg (n : USize) (x : @& FloatArray) : FloatArray

/-- Element-wise exp -/
@[extern "scilean_metal_exp"]
opaque exp (n : USize) (x : @& FloatArray) : FloatArray

/-- Element-wise exp2 (2^x) -/
@[extern "scilean_metal_exp2"]
opaque exp2 (n : USize) (x : @& FloatArray) : FloatArray

/-- Element-wise natural log -/
@[extern "scilean_metal_log"]
opaque log (n : USize) (x : @& FloatArray) : FloatArray

/-- Element-wise log2 -/
@[extern "scilean_metal_log2"]
opaque log2 (n : USize) (x : @& FloatArray) : FloatArray

/-- Element-wise sin -/
@[extern "scilean_metal_sin"]
opaque sin (n : USize) (x : @& FloatArray) : FloatArray

/-- Element-wise cos -/
@[extern "scilean_metal_cos"]
opaque cos (n : USize) (x : @& FloatArray) : FloatArray

/-- Element-wise sqrt -/
@[extern "scilean_metal_sqrt"]
opaque sqrt (n : USize) (x : @& FloatArray) : FloatArray

/-- Element-wise reciprocal (1/x) -/
@[extern "scilean_metal_reciprocal"]
opaque reciprocal (n : USize) (x : @& FloatArray) : FloatArray

/-- Element-wise ReLU: max(0, x) -/
@[extern "scilean_metal_relu"]
opaque relu (n : USize) (x : @& FloatArray) : FloatArray

/-- Element-wise sigmoid: 1/(1+exp(-x)) -/
@[extern "scilean_metal_sigmoid"]
opaque sigmoid (n : USize) (x : @& FloatArray) : FloatArray

/-- Element-wise tanh -/
@[extern "scilean_metal_tanh"]
opaque tanh (n : USize) (x : @& FloatArray) : FloatArray

/-! ## Binary Operations -/

/-- Element-wise addition -/
@[extern "scilean_metal_add"]
opaque add (n : USize) (a b : @& FloatArray) : FloatArray

/-- Element-wise subtraction -/
@[extern "scilean_metal_sub"]
opaque sub (n : USize) (a b : @& FloatArray) : FloatArray

/-- Element-wise multiplication -/
@[extern "scilean_metal_mul"]
opaque mul (n : USize) (a b : @& FloatArray) : FloatArray

/-- Element-wise division -/
@[extern "scilean_metal_div"]
opaque div (n : USize) (a b : @& FloatArray) : FloatArray

/-- Element-wise maximum -/
@[extern "scilean_metal_max"]
opaque max (n : USize) (a b : @& FloatArray) : FloatArray

/-- Element-wise minimum -/
@[extern "scilean_metal_min"]
opaque min (n : USize) (a b : @& FloatArray) : FloatArray

/-! ## Reduction Operations -/

/-- Sum all elements -/
@[extern "scilean_metal_reduce_sum"]
opaque reduceSum (n : USize) (x : @& FloatArray) : Float

/-- Maximum of all elements -/
@[extern "scilean_metal_reduce_max"]
opaque reduceMax (n : USize) (x : @& FloatArray) : Float

/-- Minimum of all elements -/
@[extern "scilean_metal_reduce_min"]
opaque reduceMin (n : USize) (x : @& FloatArray) : Float

/-! ## Other Operations -/

/-- Fill array with constant value -/
@[extern "scilean_metal_fill"]
opaque fill (n : USize) (value : Float) : FloatArray

/-- KMeans loss: sum of squared distances from each point to its nearest centroid -/
@[extern "scilean_metal_kmeans"]
opaque kmeans (d n k : USize) (points centroids : @& FloatArray) : Float

end SciLean.Metal

-- Float32 Metal Operations (Native - No Conversion)
-- ByteArray directly contains float data

namespace SciLean.Metal.Float32

-- Matrix multiply on GPU (Float32): C = A * B. A is m x k, B is k x n.
@[extern "scilean_metal_gemm_f32"]
opaque gemm (m k n : USize) (A B : @& ByteArray) : ByteArray

-- Tiled matrix multiply on GPU (Float32): optimized with 32x32 shared memory tiles
@[extern "scilean_metal_gemm_tiled_f32"]
opaque gemmTiled (m k n : USize) (A B : @& ByteArray) : ByteArray

-- Simdgroup matrix multiply on GPU (Float32): uses Apple Silicon's hardware matrix units
@[extern "scilean_metal_gemm_simd_f32"]
opaque gemmSimd (m k n : USize) (A B : @& ByteArray) : ByteArray

-- Optimized simdgroup GEMM with shared memory prefetch (Float32)
-- Improvements: double-buffered shared memory, 64×64 tiles, better occupancy
@[extern "scilean_metal_gemm_simd_opt_f32"]
opaque gemmSimdOpt (m k n : USize) (A B : @& ByteArray) : ByteArray

-- M4-optimized GEMM: float4 loads, 64×64 tiles, no bounds checks
-- REQUIRES: M, N, K are multiples of 64
-- 8 simdgroups (256 threads), 4×2 accumulator grid per simdgroup
@[extern "scilean_metal_gemm_m4_f32"]
opaque gemmM4 (m k n : USize) (A B : @& ByteArray) : ByteArray

-- M4-Pro GEMM: Double-buffered with software pipelining
-- REQUIRES: M, N, K are multiples of 64
-- Prefetches next tile while computing current
@[extern "scilean_metal_gemm_m4_pro_f32"]
opaque gemmM4Pro (m k n : USize) (A B : @& ByteArray) : ByteArray

-- M4-Max GEMM: Larger tiles (128×64) for better compute density
-- REQUIRES: M multiple of 128, N, K multiples of 64
-- 16 simdgroups (512 threads), maximum occupancy
@[extern "scilean_metal_gemm_m4_max_f32"]
opaque gemmM4Max (m k n : USize) (A B : @& ByteArray) : ByteArray

-- MPS matrix multiply on GPU (Float32): Apple's Metal Performance Shaders
-- This uses Apple's highly optimized GEMM that leverages the Neural Engine and GPU
@[extern "scilean_metal_gemm_mps_f32"]
opaque gemmMPS (m k n : USize) (A B : @& ByteArray) : ByteArray

-- Accelerate GEMM (Float32): Apple's CPU BLAS using AMX coprocessor
-- This runs on CPU but uses the AMX matrix extension for high throughput
@[extern "scilean_accelerate_gemm_f32"]
opaque gemmAccelerate (m k n : USize) (A B : @& ByteArray) : ByteArray

-- Smart GEMM (Float32): selects best kernel based on matrix size
-- Benchmarks (M4 Pro, December 2024):
--   256×256:  Simd 366 GFLOP/s (low overhead)
--   512×512:  Simd 1.5 TFLOP/s
--   1024×1024: MPS 4.0 TFLOP/s (MPS wins due to better scheduling)
--   2048×2048: MPS 12.0 TFLOP/s
--   4096×4096: MPS 20.6 TFLOP/s (near peak M4 GPU)
-- Strategy: Use MPS for anything >= 512×512, Simd for small
@[inline] def gemmAuto (m k n : USize) (A B : @& ByteArray) : ByteArray :=
  let size := m * n  -- USize multiplication, no BigNat
  let aligned := m % 8 == 0 && k % 8 == 0 && n % 8 == 0  -- USize modulo
  if size >= (512 : USize) * 512 then
    -- MPS dominates for medium+ matrices (4-20 TFLOP/s)
    gemmMPS m k n A B
  else if aligned && size >= (256 : USize) * 256 then
    -- Simd for small aligned matrices
    gemmSimd m k n A B
  else if size >= (128 : USize) * 128 then
    -- Tiled for smaller or non-aligned
    gemmTiled m k n A B
  else
    gemm m k n A B

/-! ## BLAS Level 1 Operations -/

-- AXPY: y = a*x + y (in-place update)
-- All parameters as ByteArray for zero-copy FFI
@[extern "scilean_metal_axpy_f32"]
opaque axpy (n : USize) (a x y : @& ByteArray) : ByteArray

-- AXPBY: z = a*x + b*y (creates new output)
@[extern "scilean_metal_axpby_f32"]
opaque axpby (n : USize) (a x b y : @& ByteArray) : ByteArray

-- Unary Operations

@[extern "scilean_metal_neg_f32"]
opaque neg (n : USize) (x : @& ByteArray) : ByteArray

@[extern "scilean_metal_exp2_f32"]
opaque exp2 (n : USize) (x : @& ByteArray) : ByteArray

@[extern "scilean_metal_log2_f32"]
opaque log2 (n : USize) (x : @& ByteArray) : ByteArray

@[extern "scilean_metal_sin_f32"]
opaque sin (n : USize) (x : @& ByteArray) : ByteArray

@[extern "scilean_metal_sqrt_f32"]
opaque sqrt (n : USize) (x : @& ByteArray) : ByteArray

@[extern "scilean_metal_reciprocal_f32"]
opaque reciprocal (n : USize) (x : @& ByteArray) : ByteArray

-- Binary Operations

@[extern "scilean_metal_add_f32"]
opaque add (n : USize) (a b : @& ByteArray) : ByteArray

@[extern "scilean_metal_sub_f32"]
opaque sub (n : USize) (a b : @& ByteArray) : ByteArray

@[extern "scilean_metal_mul_f32"]
opaque mul (n : USize) (a b : @& ByteArray) : ByteArray

@[extern "scilean_metal_div_f32"]
opaque div (n : USize) (a b : @& ByteArray) : ByteArray

@[extern "scilean_metal_max_f32"]
opaque max (n : USize) (a b : @& ByteArray) : ByteArray

@[extern "scilean_metal_min_f32"]
opaque min (n : USize) (a b : @& ByteArray) : ByteArray

-- Reduction Operations

@[extern "scilean_metal_reduce_sum_f32"]
opaque reduceSum (n : USize) (x : @& ByteArray) : Float32

@[extern "scilean_metal_reduce_max_f32"]
opaque reduceMax (n : USize) (x : @& ByteArray) : Float32

@[extern "scilean_metal_reduce_min_f32"]
opaque reduceMin (n : USize) (x : @& ByteArray) : Float32

-- Fill

@[extern "scilean_metal_fill_f32"]
opaque fill (n : USize) (value : Float32) : ByteArray

-- Fused Operations

-- Fused Softmax: softmax(x) = exp(x - max(x)) / sum(exp(x - max(x)))
-- Single GPU dispatch with optimized memory access
@[extern "scilean_metal_softmax_f32"]
opaque softmaxFused (n : USize) (x : @& ByteArray) : ByteArray

-- Softmax (multi-pass fallback implementation)
def softmax (sz : USize) (x : ByteArray) : ByteArray :=
  -- Use fused version if available
  softmaxFused sz x

-- Bias + ReLU: output = max(0, input + bias)
-- n = total elements, stride = features per sample (bias length)
-- Useful for dense layers: y = relu(Wx + b)
@[extern "scilean_metal_bias_relu_f32"]
opaque biasRelu (n stride : USize) (input bias : @& ByteArray) : ByteArray

-- Bias + GELU: output = GELU(input + bias)
-- GELU approximation: x * 0.5 * (1 + tanh(sqrt(2/π) * (x + 0.044715 * x³)))
-- Used in transformer models like GPT/BERT
@[extern "scilean_metal_bias_gelu_f32"]
opaque biasGelu (n stride : USize) (input bias : @& ByteArray) : ByteArray

-- Layer Normalization: output = gamma * (input - mean) / sqrt(var + eps) + beta
-- n = total elements, hiddenSize = features per sample
-- gamma/beta are learned scale/shift parameters
@[extern "scilean_metal_layer_norm_f32"]
opaque layerNorm (n hiddenSize : USize) (input gamma beta : @& ByteArray) : ByteArray

/-! ## Attention Operations -/

-- Flash Attention (single head): output = softmax(Q*K^T / sqrt(d)) * V
-- Q, K, V: [seq_len, head_dim] stored as ByteArray (Float32)
-- Returns output: [seq_len, head_dim]
-- Uses online softmax for memory efficiency (no full attention matrix materialized)
@[extern "scilean_metal_flash_attention_f32"]
opaque flashAttention (seqLen headDim : USize) (Q K V : @& ByteArray) : ByteArray

-- Flash Attention with causal mask (for autoregressive models)
-- Only attends to positions <= current position
-- Used for GPT-style decoder-only models
@[extern "scilean_metal_flash_attention_causal_f32"]
opaque flashAttentionCausal (seqLen headDim : USize) (Q K V : @& ByteArray) : ByteArray

-- Multi-head attention
-- Q, K, V: [batch, num_heads, seq_len, head_dim]
-- Returns: [batch, num_heads, seq_len, head_dim]
@[extern "scilean_metal_attention_multihead_f32"]
opaque attentionMultiHead (batchSize numHeads seqLen headDim : USize)
    (Q K V : @& ByteArray) : ByteArray

-- Batched softmax (row-wise)
-- Input: [numRows, rowSize], applies softmax to each row independently
-- Commonly used for attention weights
@[extern "scilean_metal_softmax_batched_f32"]
opaque softmaxBatched (numRows rowSize : USize) (x : @& ByteArray) : ByteArray

/-! ## Convolutional Neural Network Operations -/

-- Conv2D: 2D convolution with optional fused ReLU
-- Input: NCHW format [batch, in_channels, height, width]
-- Kernel: OIHW format [out_channels, in_channels, kernel_h, kernel_w]
-- Bias: [out_channels]
-- Output: NCHW format [batch, out_channels, out_height, out_width]
-- where out_height = (in_height + 2*pad_h - kernel_h) / stride_h + 1
@[extern "scilean_metal_conv2d_f32"]
opaque conv2d (batchSize inChannels outChannels : USize)
    (inHeight inWidth : USize)
    (kernelH kernelW : USize)
    (strideH strideW : USize)
    (padH padW : USize)
    (useRelu : UInt8)
    (input kernel bias : @& ByteArray) : ByteArray

-- Conv2D Fast: Optimized 2D convolution
-- Uses specialized 3x3 kernel with unrolled loops when applicable (3x3, stride 1, pad 1)
-- Falls back to naive implementation otherwise
@[extern "scilean_metal_conv2d_fast_f32"]
opaque conv2dFast (batchSize inChannels outChannels : USize)
    (inHeight inWidth : USize)
    (kernelH kernelW : USize)
    (strideH strideW : USize)
    (padH padW : USize)
    (useRelu : UInt8)
    (input kernel bias : @& ByteArray) : ByteArray

-- Conv2D GEMM: Convolution using im2col + GEMM approach
-- Converts conv to matrix multiply for better use of GEMM optimizations
-- May be faster for large convolutions due to optimized GEMM kernel
@[extern "scilean_metal_conv2d_gemm_f32"]
opaque conv2dGemm (batchSize inChannels outChannels : USize)
    (inHeight inWidth : USize)
    (kernelH kernelW : USize)
    (strideH strideW : USize)
    (padH padW : USize)
    (useRelu : UInt8)
    (input kernel bias : @& ByteArray) : ByteArray

-- MaxPool2D: Max pooling over 2D input
-- Input: NCHW format [batch, channels, height, width]
-- Output: NCHW format [batch, channels, out_height, out_width]
-- where out_height = (in_height - pool_h) / stride_h + 1
@[extern "scilean_metal_maxpool2d_f32"]
opaque maxPool2d (batchSize channels : USize)
    (inHeight inWidth : USize)
    (poolH poolW : USize)
    (strideH strideW : USize)
    (input : @& ByteArray) : ByteArray

-- AvgPool2D: Average pooling over 2D input
-- Input: NCHW format [batch, channels, height, width]
-- Output: NCHW format [batch, channels, out_height, out_width]
@[extern "scilean_metal_avgpool2d_f32"]
opaque avgPool2d (batchSize channels : USize)
    (inHeight inWidth : USize)
    (poolH poolW : USize)
    (strideH strideW : USize)
    (input : @& ByteArray) : ByteArray

-- Global Average Pooling: Reduces spatial dimensions to 1x1
-- Input: NCHW format [batch, channels, height, width]
-- Output: [batch, channels]
@[extern "scilean_metal_global_avgpool2d_f32"]
opaque globalAvgPool2d (batchSize channels height width : USize)
    (input : @& ByteArray) : ByteArray

-- BatchNorm2D inference: Batch normalization for CNN inference
-- Computes: y = gamma * (x - mean) / sqrt(var + eps) + beta
-- Input: NCHW format [batch, channels, height, width]
-- gamma, beta, mean, var: [channels]
-- applyRelu: 1 to fuse ReLU, 0 otherwise
@[extern "scilean_metal_batchnorm2d_f32"]
opaque batchNorm2d (batchSize channels height width : USize)
    (eps : Float32) (applyRelu : UInt8)
    (input gamma beta mean var : @& ByteArray) : ByteArray

end SciLean.Metal.Float32
