#include <lean/lean.h>

#include <cblas.h>

/**
 * Helper to ensure exclusive access to float array
 */
static void ensure_exclusive_float_array(lean_object ** X){
  if (!lean_is_exclusive(*X)) {
    *X = lean_copy_float_array(*X);
  }
}

/**
 * dgemm_simple - Simplified GEMM for row-major C = alpha*A*B + beta*C
 *
 * For matrices A[M,K], B[K,N] -> C[M,N]
 *
 * This is a convenience wrapper that assumes:
 * - Row-major order
 * - No transpose
 * - Standard leading dimensions (lda=K, ldb=N, ldc=N)
 */
LEAN_EXPORT lean_obj_res scilean_cblas_dgemm_simple(
    const size_t M, const size_t N, const size_t K,
    const double alpha,
    const b_lean_obj_arg A,
    const b_lean_obj_arg B,
    const double beta,
    lean_obj_arg C) {

  ensure_exclusive_float_array(&C);

  cblas_dgemm(CblasRowMajor,
              CblasNoTrans, CblasNoTrans,
              (int)M, (int)N, (int)K,
              alpha,
              lean_float_array_cptr(A), (int)K,
              lean_float_array_cptr(B), (int)N,
              beta,
              lean_float_array_cptr(C), (int)N);

  return C;
}
