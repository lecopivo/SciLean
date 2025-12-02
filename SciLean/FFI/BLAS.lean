/-!
# BLAS Level 3 FFI

FFI bindings for BLAS Level 3 operations (matrix-matrix).
-/

namespace SciLean.BLAS

/--
dgemm - Double precision GEneral Matrix Multiplication

Computes: `C := alpha * A * B + beta * C`

For row-major `A[M,K]`, `B[K,N]`, `C[M,N]`

C is modified in place.
-/
@[extern "scilean_cblas_dgemm_simple"]
opaque dgemmSimple (M N K : USize) (alpha : Float)
    (A : @& FloatArray) (B : @& FloatArray)
    (beta : Float) (C : FloatArray) : FloatArray

end SciLean.BLAS
