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
--   1024×1024: Simd 6.3 TFLOP/s >> MPS 3.2 TFLOP/s (Simd wins 2x)
--   2048×2048: MPS 11.0 TFLOP/s > Simd 8.6 TFLOP/s (MPS wins 1.28x)
--   4096×4096: MPS 12.9 TFLOP/s (MPS amortizes launch overhead)
-- Crossover: ~1536×1536, use 1.5M elements as threshold
-- NOTE: Using native USize arithmetic to avoid BigNat allocation overhead
@[inline] def gemmAuto (m k n : USize) (A B : @& ByteArray) : ByteArray :=
  let size := m * n  -- USize multiplication, no BigNat
  let aligned := m % 8 == 0 && k % 8 == 0 && n % 8 == 0  -- USize modulo
  if size >= (1536 : USize) * 1536 then
    -- MPS dominates for large matrices (10+ TFLOP/s)
    gemmMPS m k n A B
  else if aligned && size >= (256 : USize) * 256 then
    -- Simdgroup for medium aligned matrices (6-8 TFLOP/s)
    gemmSimd m k n A B
  else if size >= (128 : USize) * 128 then
    -- Tiled for smaller or non-aligned matrices (~3 TFLOP/s)
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

-- Softmax: softmax(x) = exp(x - max(x)) / sum(exp(x - max(x)))
-- Currently implemented using multiple GPU passes.
def softmax (sz : USize) (x : ByteArray) : ByteArray :=
  -- Find max for numerical stability
  let maxVal := reduceMax sz x
  -- Create array filled with max value
  let maxArr := fill sz maxVal
  -- Subtract max: x - max
  let shifted := sub sz x maxArr
  -- Compute exp using exp2: exp(x) = 2^(x * log2(e)), log2(e) ≈ 1.4427
  let log2e : Float32 := (1.4426950408889634 : Float32)  -- log2(e)
  let log2eArr := fill sz log2e
  let scaledShifted := mul sz shifted log2eArr
  let expVals := exp2 sz scaledShifted
  -- Sum the exp values
  let sumVal := reduceSum sz expVals
  -- Normalize: exp / sum
  let sumArr := fill sz sumVal
  div sz expVals sumArr

end SciLean.Metal.Float32
