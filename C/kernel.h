/*
 * SciLean Kernel - Minimal dtype-parametric tensor operations
 *
 * Design principles:
 * - All arrays are contiguous (JAX-style, no arbitrary strides)
 * - DType parameter selects numeric format at runtime
 * - Row-major layout for matrices
 */

#ifndef SCILEAN_KERNEL_H
#define SCILEAN_KERNEL_H

#include <stddef.h>
#include <stdint.h>
#include <lean/lean.h>

/* Data type enum - must match SciLean.Kernel.DType */
typedef enum {
    DTYPE_F64     = 0,   /* Float64 (8 bytes) */
    DTYPE_F32     = 1,   /* Float32 (4 bytes) */
    DTYPE_F16     = 2,   /* IEEE Float16 (2 bytes) */
    DTYPE_BF16    = 3,   /* bfloat16 (2 bytes) */
    DTYPE_F8_E4M3 = 4,   /* FP8 E4M3 (1 byte) */
    DTYPE_F8_E5M2 = 5,   /* FP8 E5M2 (1 byte) */
    DTYPE_I32     = 6,   /* Int32 (4 bytes) */
    DTYPE_I16     = 7,   /* Int16 (2 bytes) */
    DTYPE_I8      = 8,   /* Int8 (1 byte) */
    DTYPE_U8      = 9,   /* UInt8 (1 byte) */
} DType;

/* Returns byte size for a dtype */
static inline size_t dtype_size(DType dt) {
    switch (dt) {
        case DTYPE_F64: return 8;
        case DTYPE_F32: return 4;
        case DTYPE_F16: return 2;
        case DTYPE_BF16: return 2;
        case DTYPE_F8_E4M3: return 1;
        case DTYPE_F8_E5M2: return 1;
        case DTYPE_I32: return 4;
        case DTYPE_I16: return 2;
        case DTYPE_I8: return 1;
        case DTYPE_U8: return 1;
        default: return 0;
    }
}

/*
 * ============================================================================
 * Tier 0: Memory Operations
 * ============================================================================
 */

/* Note: Memory allocation/deallocation handled by Lean's ByteArray.
 * These functions operate on ByteArray data directly via lean_byte_array_cptr.
 */

/* Copy n elements from src to dst */
LEAN_EXPORT lean_obj_res k_copy(lean_obj_arg dst, b_lean_obj_arg src,
                                 size_t n, uint8_t dt);

/*
 * ============================================================================
 * Tier 1: Elementwise Binary Operations
 * dst = a ⊕ b, all contiguous, same dtype
 * ============================================================================
 */

LEAN_EXPORT lean_obj_res k_add(lean_obj_arg dst, b_lean_obj_arg a,
                                b_lean_obj_arg b, size_t n, uint8_t dt);

LEAN_EXPORT lean_obj_res k_sub(lean_obj_arg dst, b_lean_obj_arg a,
                                b_lean_obj_arg b, size_t n, uint8_t dt);

LEAN_EXPORT lean_obj_res k_mul(lean_obj_arg dst, b_lean_obj_arg a,
                                b_lean_obj_arg b, size_t n, uint8_t dt);

LEAN_EXPORT lean_obj_res k_div(lean_obj_arg dst, b_lean_obj_arg a,
                                b_lean_obj_arg b, size_t n, uint8_t dt);

/*
 * ============================================================================
 * Tier 2: Elementwise Unary Operations
 * dst = f(x)
 * ============================================================================
 */

LEAN_EXPORT lean_obj_res k_neg(lean_obj_arg dst, b_lean_obj_arg x,
                                size_t n, uint8_t dt);

LEAN_EXPORT lean_obj_res k_abs(lean_obj_arg dst, b_lean_obj_arg x,
                                size_t n, uint8_t dt);

LEAN_EXPORT lean_obj_res k_exp(lean_obj_arg dst, b_lean_obj_arg x,
                                size_t n, uint8_t dt);

LEAN_EXPORT lean_obj_res k_log(lean_obj_arg dst, b_lean_obj_arg x,
                                size_t n, uint8_t dt);

LEAN_EXPORT lean_obj_res k_sqrt(lean_obj_arg dst, b_lean_obj_arg x,
                                 size_t n, uint8_t dt);

LEAN_EXPORT lean_obj_res k_tanh(lean_obj_arg dst, b_lean_obj_arg x,
                                 size_t n, uint8_t dt);

/*
 * ============================================================================
 * Tier 3: Reductions
 * ============================================================================
 */

/* Sum all elements, return scalar in same dtype */
LEAN_EXPORT double k_sum(b_lean_obj_arg x, size_t n, uint8_t dt);

/* Max of all elements */
LEAN_EXPORT double k_max(b_lean_obj_arg x, size_t n, uint8_t dt);

/* Index of maximum element */
LEAN_EXPORT size_t k_argmax(b_lean_obj_arg x, size_t n, uint8_t dt);

/*
 * ============================================================================
 * Tier 4: Contractions (THE hot path)
 * ============================================================================
 */

/* C[m,n] = alpha * A[m,k] @ B[k,n] + beta * C[m,n]
 * Row-major, contiguous. */
LEAN_EXPORT lean_obj_res k_gemm(lean_obj_arg C, b_lean_obj_arg A, b_lean_obj_arg B,
                                 size_t m, size_t k, size_t n,
                                 double alpha, double beta, uint8_t dt);

/* y[m] = A[m,n] @ x[n] */
LEAN_EXPORT lean_obj_res k_gemv(lean_obj_arg y, b_lean_obj_arg A, b_lean_obj_arg x,
                                 size_t m, size_t n, uint8_t dt);

/*
 * ============================================================================
 * Tier 5: Fused Operations (Numerical stability)
 * ============================================================================
 */

/* Numerically stable softmax: dst[i] = exp(x[i] - max(x)) / sum(exp(x - max(x))) */
LEAN_EXPORT lean_obj_res k_softmax(lean_obj_arg dst, b_lean_obj_arg x,
                                    size_t n, uint8_t dt);

/* y = alpha*x + beta*y (fused for memory bandwidth) */
LEAN_EXPORT lean_obj_res k_axpby(lean_obj_arg y, double alpha, b_lean_obj_arg x,
                                  double beta, size_t n, uint8_t dt);

/*
 * ============================================================================
 * Tier 6: Index Permutation (Cache-efficient layout transforms)
 * ============================================================================
 */

/* Transpose 2D matrix: dst[j,i] = src[i,j] */
LEAN_EXPORT lean_obj_res k_transpose(lean_obj_arg dst, b_lean_obj_arg src,
                                      size_t rows, size_t cols, uint8_t dt);

/* General axis permutation: perm[i] = which src axis becomes dst axis i */
LEAN_EXPORT lean_obj_res k_permute(lean_obj_arg dst, b_lean_obj_arg src,
                                    size_t ndim, b_lean_obj_arg shape,
                                    b_lean_obj_arg perm, uint8_t dt);

/*
 * ============================================================================
 * Tier 7: Random Number Generation
 * ============================================================================
 */

/* Seed the RNG state */
LEAN_EXPORT void k_rng_seed(uint64_t seed);

/* Fill buffer with uniform random in [0, 1) */
LEAN_EXPORT lean_obj_res k_rand_uniform(lean_obj_arg dst, size_t n, uint8_t dt);

/* Fill buffer with standard normal (mean=0, std=1) */
LEAN_EXPORT lean_obj_res k_rand_normal(lean_obj_arg dst, size_t n, uint8_t dt);

#endif /* SCILEAN_KERNEL_H */
