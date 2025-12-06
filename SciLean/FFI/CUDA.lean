/-
  CUDA Backend for SciLean
  Mirrors Metal.lean structure for NVIDIA GPUs

  Build requirements:
  - CUDA toolkit (nvcc, cublas)
  - Linux (CUDA not available on macOS)

  Usage:
    import SciLean.FFI.CUDA
    #eval CUDA.isAvailable ()  -- Check if CUDA GPU available
-/

namespace SciLean.CUDA

/-! ## Availability Check -/

@[extern "scilean_cuda_available"]
opaque isAvailable : Unit → Bool

@[extern "scilean_cuda_device_name"]
opaque deviceName : Unit → String

/-- Run computation on CUDA if available, fallback otherwise -/
@[inline] def withGPU [Inhabited α] (cudaFn : Unit → α) (fallback : Unit → α) : α :=
  if isAvailable () then cudaFn () else fallback ()

/-! ## GEMM Operations (Float32 via ByteArray) -/

/-- Naive GEMM: C = A × B (for benchmarking) -/
@[extern "scilean_cuda_gemm_naive"]
opaque gemmNaive (m k n : USize) (A B : @& ByteArray) : ByteArray

/-- Tiled GEMM with shared memory: C = A × B -/
@[extern "scilean_cuda_gemm_tiled"]
opaque gemmTiled (m k n : USize) (A B : @& ByteArray) : ByteArray

/-- cuBLAS GEMM (highly optimized): C = A × B -/
@[extern "scilean_cuda_gemm_cublas"]
opaque gemmCuBLAS (m k n : USize) (A B : @& ByteArray) : ByteArray

/-- Smart GEMM: selects best kernel based on size -/
-- cuBLAS is almost always best on NVIDIA, but has launch overhead for tiny matrices
@[inline] def gemmAuto (m k n : USize) (A B : @& ByteArray) : ByteArray :=
  let size := m * n
  if size >= (128 : USize) * 128 then
    -- cuBLAS dominates for anything non-trivial
    gemmCuBLAS m k n A B
  else
    -- Tiled for tiny matrices (avoid cuBLAS overhead)
    gemmTiled m k n A B

/-! ## Element-wise Operations -/

@[extern "scilean_cuda_add"]
opaque add (n : USize) (A B : @& ByteArray) : ByteArray

/-! ## Reduction Operations -/

@[extern "scilean_cuda_reduce_sum"]
opaque reduceSum (n : USize) (A : @& ByteArray) : Float32

end SciLean.CUDA
