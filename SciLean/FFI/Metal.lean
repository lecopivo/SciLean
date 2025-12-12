/-
Metal GPU Backend

Low-level FFI bindings to Metal compute shaders for GPU acceleration.
These operate on raw FloatArrays for minimal dependencies.

Operations: unary (neg, exp, log, etc), binary (add, mul), reductions (sum, max),
matrix (gemv, gemm variants), fill, kmeans.

Performance on M4: gemmSimd ~10 TFLOP/s, gemmTiled ~6 TFLOP/s at 2048x2048.
-/

namespace SciLean.Metal

/-! ## Core -/

/-- Check if Metal GPU acceleration is available -/
@[extern "scilean_metal_available"]
opaque isAvailable : Unit → Bool

/-- Run computation on GPU if available, otherwise fallback to CPU -/
def withGPU [Inhabited α] (gpuFn cpuFn : Unit → α) : α :=
  if isAvailable () then gpuFn () else cpuFn ()

/-! ## GPU-Resident Buffers

GPU-resident buffers stay on the GPU between operations, eliminating the overhead
of copying data to/from CPU memory on every operation. This is critical for
performance in ML workloads where data flows through many operations.

Usage pattern:
```
-- Upload once
let weights ← GpuBuffer.fromByteArray weightData
let input ← GpuBuffer.fromByteArray inputData

-- Chain operations on GPU (no copies!)
let h1 ← GpuBuffer.gemm weights input m k n
let h2 ← GpuBuffer.relu h1

-- Download only final result
let output ← h2.toByteArray
```
-/

/-- Opaque handle to a GPU-resident Metal buffer.
    Data stays on GPU until explicitly downloaded. -/
opaque GpuBufferPointed : NonemptyType
def GpuBuffer : Type := GpuBufferPointed.type
instance : Nonempty GpuBuffer := GpuBufferPointed.property

namespace GpuBuffer

/-- Allocate an uninitialized GPU buffer of given size (in floats) -/
@[extern "scilean_gpu_alloc_f32"]
opaque alloc (numFloats : USize) : IO GpuBuffer

/-- Upload ByteArray (Float32 data) to GPU -/
@[extern "scilean_gpu_upload_f32"]
opaque fromByteArray (data : @& ByteArray) : IO GpuBuffer

/-- Download GPU buffer to ByteArray -/
@[extern "scilean_gpu_download_f32"]
opaque toByteArray (buf : @& GpuBuffer) : IO ByteArray

/-- Get size of buffer in bytes -/
@[extern "scilean_gpu_size"]
opaque sizeBytes (buf : @& GpuBuffer) : USize

/-- Free GPU buffer (optional - will be freed on GC anyway) -/
@[extern "scilean_gpu_free"]
opaque free (buf : GpuBuffer) : IO Unit

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

end GpuBuffer

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
