/-!
# Metal GPU Backend

Low-level FFI bindings to Metal compute shaders for GPU acceleration.
These operate on raw FloatArrays for minimal dependencies.
-/

namespace SciLean.Metal

/-- Check if Metal GPU acceleration is available -/
@[extern "scilean_metal_available"]
opaque isAvailable : Unit → Bool

/-- KMeans loss computation on GPU
    Returns the sum of squared distances from each point to its nearest centroid -/
@[extern "scilean_metal_kmeans"]
opaque kmeans (d n k : USize) (points centroids : @& FloatArray) : Float

/-- Matrix-vector multiply on GPU: y = A * x
    A is m×n, x is n-dimensional, returns m-dimensional y -/
@[extern "scilean_metal_gemv"]
opaque gemv (m n : USize) (A x : @& FloatArray) : FloatArray

/-- Matrix multiply on GPU: C = A * B
    A is m×k, B is k×n, returns m×n matrix C as flat array -/
@[extern "scilean_metal_gemm"]
opaque gemm (m k n : USize) (A B : @& FloatArray) : FloatArray

/-- Element-wise addition on GPU -/
@[extern "scilean_metal_add"]
opaque add (n : USize) (a b : @& FloatArray) : FloatArray

/-- Run computation on GPU if available, otherwise fallback to CPU -/
def withGPU [Inhabited α] (gpuFn cpuFn : Unit → α) : α :=
  if isAvailable () then gpuFn () else cpuFn ()

end SciLean.Metal
