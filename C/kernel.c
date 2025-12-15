/*
 * SciLean Kernel - Dtype-parametric tensor operations
 *
 * Currently implements: f64, f32
 * TODO: f16, bf16, fp8, int types
 */

#include "kernel.h"
#include <math.h>
#include <string.h>
#include <stdlib.h>

/* ============================================================================
 * Internal helpers
 * ============================================================================ */

/* Ensure ByteArray is exclusive (for mutation) */
static inline lean_obj_res ensure_exclusive(lean_obj_arg arr) {
    if (lean_is_exclusive(arr)) {
        return arr;
    }
    size_t size = lean_sarray_size(arr);
    lean_obj_res new_arr = lean_alloc_sarray(1, size, size);
    memcpy(lean_sarray_cptr(new_arr), lean_sarray_cptr(arr), size);
    lean_dec_ref(arr);
    return new_arr;
}

/* Get C pointer to ByteArray data */
static inline void* byte_array_ptr(b_lean_obj_arg arr) {
    return (void*)lean_sarray_cptr(arr);
}

/* ============================================================================
 * Tier 0: Memory Operations
 * ============================================================================ */

LEAN_EXPORT lean_obj_res k_copy(lean_obj_arg dst, b_lean_obj_arg src,
                                 size_t n, uint8_t dt) {
    dst = ensure_exclusive(dst);
    size_t bytes = n * dtype_size((DType)dt);
    memcpy(byte_array_ptr(dst), byte_array_ptr(src), bytes);
    return dst;
}

/* ============================================================================
 * Tier 1: Elementwise Binary Operations
 * ============================================================================ */

#define DEFINE_BINARY_OP(name, op)                                              \
LEAN_EXPORT lean_obj_res k_##name(lean_obj_arg dst, b_lean_obj_arg a,           \
                                   b_lean_obj_arg b, size_t n, uint8_t dt) {    \
    dst = ensure_exclusive(dst);                                                \
    switch ((DType)dt) {                                                        \
        case DTYPE_F64: {                                                       \
            double* d = (double*)byte_array_ptr(dst);                           \
            const double* pa = (const double*)byte_array_ptr(a);                \
            const double* pb = (const double*)byte_array_ptr(b);                \
            for (size_t i = 0; i < n; i++) d[i] = pa[i] op pb[i];               \
            break;                                                              \
        }                                                                       \
        case DTYPE_F32: {                                                       \
            float* d = (float*)byte_array_ptr(dst);                             \
            const float* pa = (const float*)byte_array_ptr(a);                  \
            const float* pb = (const float*)byte_array_ptr(b);                  \
            for (size_t i = 0; i < n; i++) d[i] = pa[i] op pb[i];               \
            break;                                                              \
        }                                                                       \
        default:                                                                \
            /* TODO: other dtypes */                                            \
            break;                                                              \
    }                                                                           \
    return dst;                                                                 \
}

DEFINE_BINARY_OP(add, +)
DEFINE_BINARY_OP(sub, -)
DEFINE_BINARY_OP(mul, *)
DEFINE_BINARY_OP(div, /)

#undef DEFINE_BINARY_OP

/* ============================================================================
 * Tier 2: Elementwise Unary Operations
 * ============================================================================ */

LEAN_EXPORT lean_obj_res k_neg(lean_obj_arg dst, b_lean_obj_arg x,
                                size_t n, uint8_t dt) {
    dst = ensure_exclusive(dst);
    switch ((DType)dt) {
        case DTYPE_F64: {
            double* d = (double*)byte_array_ptr(dst);
            const double* px = (const double*)byte_array_ptr(x);
            for (size_t i = 0; i < n; i++) d[i] = -px[i];
            break;
        }
        case DTYPE_F32: {
            float* d = (float*)byte_array_ptr(dst);
            const float* px = (const float*)byte_array_ptr(x);
            for (size_t i = 0; i < n; i++) d[i] = -px[i];
            break;
        }
        default: break;
    }
    return dst;
}

LEAN_EXPORT lean_obj_res k_abs(lean_obj_arg dst, b_lean_obj_arg x,
                                size_t n, uint8_t dt) {
    dst = ensure_exclusive(dst);
    switch ((DType)dt) {
        case DTYPE_F64: {
            double* d = (double*)byte_array_ptr(dst);
            const double* px = (const double*)byte_array_ptr(x);
            for (size_t i = 0; i < n; i++) d[i] = fabs(px[i]);
            break;
        }
        case DTYPE_F32: {
            float* d = (float*)byte_array_ptr(dst);
            const float* px = (const float*)byte_array_ptr(x);
            for (size_t i = 0; i < n; i++) d[i] = fabsf(px[i]);
            break;
        }
        default: break;
    }
    return dst;
}

#define DEFINE_UNARY_MATH(name, f64_fn, f32_fn)                                 \
LEAN_EXPORT lean_obj_res k_##name(lean_obj_arg dst, b_lean_obj_arg x,           \
                                   size_t n, uint8_t dt) {                      \
    dst = ensure_exclusive(dst);                                                \
    switch ((DType)dt) {                                                        \
        case DTYPE_F64: {                                                       \
            double* d = (double*)byte_array_ptr(dst);                           \
            const double* px = (const double*)byte_array_ptr(x);                \
            for (size_t i = 0; i < n; i++) d[i] = f64_fn(px[i]);                \
            break;                                                              \
        }                                                                       \
        case DTYPE_F32: {                                                       \
            float* d = (float*)byte_array_ptr(dst);                             \
            const float* px = (const float*)byte_array_ptr(x);                  \
            for (size_t i = 0; i < n; i++) d[i] = f32_fn(px[i]);                \
            break;                                                              \
        }                                                                       \
        default: break;                                                         \
    }                                                                           \
    return dst;                                                                 \
}

DEFINE_UNARY_MATH(exp, exp, expf)
DEFINE_UNARY_MATH(log, log, logf)
DEFINE_UNARY_MATH(sqrt, sqrt, sqrtf)
DEFINE_UNARY_MATH(tanh, tanh, tanhf)

#undef DEFINE_UNARY_MATH

/* ============================================================================
 * Tier 3: Reductions
 * ============================================================================ */

LEAN_EXPORT double k_sum(b_lean_obj_arg x, size_t n, uint8_t dt) {
    double sum = 0.0;
    switch ((DType)dt) {
        case DTYPE_F64: {
            const double* px = (const double*)byte_array_ptr(x);
            for (size_t i = 0; i < n; i++) sum += px[i];
            break;
        }
        case DTYPE_F32: {
            const float* px = (const float*)byte_array_ptr(x);
            for (size_t i = 0; i < n; i++) sum += (double)px[i];
            break;
        }
        default: break;
    }
    return sum;
}

LEAN_EXPORT double k_max(b_lean_obj_arg x, size_t n, uint8_t dt) {
    if (n == 0) return -INFINITY;
    double max_val;
    switch ((DType)dt) {
        case DTYPE_F64: {
            const double* px = (const double*)byte_array_ptr(x);
            max_val = px[0];
            for (size_t i = 1; i < n; i++) if (px[i] > max_val) max_val = px[i];
            break;
        }
        case DTYPE_F32: {
            const float* px = (const float*)byte_array_ptr(x);
            max_val = (double)px[0];
            for (size_t i = 1; i < n; i++) if (px[i] > max_val) max_val = (double)px[i];
            break;
        }
        default:
            max_val = -INFINITY;
            break;
    }
    return max_val;
}

LEAN_EXPORT size_t k_argmax(b_lean_obj_arg x, size_t n, uint8_t dt) {
    if (n == 0) return 0;
    size_t max_idx = 0;
    switch ((DType)dt) {
        case DTYPE_F64: {
            const double* px = (const double*)byte_array_ptr(x);
            double max_val = px[0];
            for (size_t i = 1; i < n; i++) {
                if (px[i] > max_val) { max_val = px[i]; max_idx = i; }
            }
            break;
        }
        case DTYPE_F32: {
            const float* px = (const float*)byte_array_ptr(x);
            float max_val = px[0];
            for (size_t i = 1; i < n; i++) {
                if (px[i] > max_val) { max_val = px[i]; max_idx = i; }
            }
            break;
        }
        default: break;
    }
    return max_idx;
}

/* ============================================================================
 * Tier 4: Contractions
 * ============================================================================ */

/* Naive GEMM: C[m,n] = alpha * A[m,k] @ B[k,n] + beta * C[m,n]
 * Row-major layout. For production, replace with BLAS call. */
LEAN_EXPORT lean_obj_res k_gemm(lean_obj_arg C, b_lean_obj_arg A, b_lean_obj_arg B,
                                 size_t m, size_t k, size_t n,
                                 double alpha, double beta, uint8_t dt) {
    C = ensure_exclusive(C);
    switch ((DType)dt) {
        case DTYPE_F64: {
            double* pc = (double*)byte_array_ptr(C);
            const double* pa = (const double*)byte_array_ptr(A);
            const double* pb = (const double*)byte_array_ptr(B);
            for (size_t i = 0; i < m; i++) {
                for (size_t j = 0; j < n; j++) {
                    double sum = 0.0;
                    for (size_t l = 0; l < k; l++) {
                        sum += pa[i * k + l] * pb[l * n + j];
                    }
                    pc[i * n + j] = alpha * sum + beta * pc[i * n + j];
                }
            }
            break;
        }
        case DTYPE_F32: {
            float* pc = (float*)byte_array_ptr(C);
            const float* pa = (const float*)byte_array_ptr(A);
            const float* pb = (const float*)byte_array_ptr(B);
            float a = (float)alpha, b = (float)beta;
            for (size_t i = 0; i < m; i++) {
                for (size_t j = 0; j < n; j++) {
                    float sum = 0.0f;
                    for (size_t l = 0; l < k; l++) {
                        sum += pa[i * k + l] * pb[l * n + j];
                    }
                    pc[i * n + j] = a * sum + b * pc[i * n + j];
                }
            }
            break;
        }
        default: break;
    }
    return C;
}

/* GEMV: y[m] = A[m,n] @ x[n] */
LEAN_EXPORT lean_obj_res k_gemv(lean_obj_arg y, b_lean_obj_arg A, b_lean_obj_arg x,
                                 size_t m, size_t n, uint8_t dt) {
    y = ensure_exclusive(y);
    switch ((DType)dt) {
        case DTYPE_F64: {
            double* py = (double*)byte_array_ptr(y);
            const double* pa = (const double*)byte_array_ptr(A);
            const double* px = (const double*)byte_array_ptr(x);
            for (size_t i = 0; i < m; i++) {
                double sum = 0.0;
                for (size_t j = 0; j < n; j++) {
                    sum += pa[i * n + j] * px[j];
                }
                py[i] = sum;
            }
            break;
        }
        case DTYPE_F32: {
            float* py = (float*)byte_array_ptr(y);
            const float* pa = (const float*)byte_array_ptr(A);
            const float* px = (const float*)byte_array_ptr(x);
            for (size_t i = 0; i < m; i++) {
                float sum = 0.0f;
                for (size_t j = 0; j < n; j++) {
                    sum += pa[i * n + j] * px[j];
                }
                py[i] = sum;
            }
            break;
        }
        default: break;
    }
    return y;
}

/* ============================================================================
 * Tier 5: Fused Operations
 * ============================================================================ */

/* Numerically stable softmax */
LEAN_EXPORT lean_obj_res k_softmax(lean_obj_arg dst, b_lean_obj_arg x,
                                    size_t n, uint8_t dt) {
    dst = ensure_exclusive(dst);
    switch ((DType)dt) {
        case DTYPE_F64: {
            double* d = (double*)byte_array_ptr(dst);
            const double* px = (const double*)byte_array_ptr(x);
            /* Find max for numerical stability */
            double max_val = px[0];
            for (size_t i = 1; i < n; i++) if (px[i] > max_val) max_val = px[i];
            /* Compute exp(x - max) and sum */
            double sum = 0.0;
            for (size_t i = 0; i < n; i++) {
                d[i] = exp(px[i] - max_val);
                sum += d[i];
            }
            /* Normalize */
            for (size_t i = 0; i < n; i++) d[i] /= sum;
            break;
        }
        case DTYPE_F32: {
            float* d = (float*)byte_array_ptr(dst);
            const float* px = (const float*)byte_array_ptr(x);
            float max_val = px[0];
            for (size_t i = 1; i < n; i++) if (px[i] > max_val) max_val = px[i];
            float sum = 0.0f;
            for (size_t i = 0; i < n; i++) {
                d[i] = expf(px[i] - max_val);
                sum += d[i];
            }
            for (size_t i = 0; i < n; i++) d[i] /= sum;
            break;
        }
        default: break;
    }
    return dst;
}

/* y = alpha*x + beta*y */
LEAN_EXPORT lean_obj_res k_axpby(lean_obj_arg y, double alpha, b_lean_obj_arg x,
                                  double beta, size_t n, uint8_t dt) {
    y = ensure_exclusive(y);
    switch ((DType)dt) {
        case DTYPE_F64: {
            double* py = (double*)byte_array_ptr(y);
            const double* px = (const double*)byte_array_ptr(x);
            for (size_t i = 0; i < n; i++) {
                py[i] = alpha * px[i] + beta * py[i];
            }
            break;
        }
        case DTYPE_F32: {
            float* py = (float*)byte_array_ptr(y);
            const float* px = (const float*)byte_array_ptr(x);
            float a = (float)alpha, b = (float)beta;
            for (size_t i = 0; i < n; i++) {
                py[i] = a * px[i] + b * py[i];
            }
            break;
        }
        default: break;
    }
    return y;
}

/* ============================================================================
 * Tier 6: Index Permutation
 * ============================================================================ */

/* Cache-blocked transpose for better performance on large matrices */
#define BLOCK_SIZE 32

LEAN_EXPORT lean_obj_res k_transpose(lean_obj_arg dst, b_lean_obj_arg src,
                                      size_t rows, size_t cols, uint8_t dt) {
    dst = ensure_exclusive(dst);
    switch ((DType)dt) {
        case DTYPE_F64: {
            double* d = (double*)byte_array_ptr(dst);
            const double* s = (const double*)byte_array_ptr(src);
            /* Cache-blocked for large matrices */
            for (size_t i0 = 0; i0 < rows; i0 += BLOCK_SIZE) {
                for (size_t j0 = 0; j0 < cols; j0 += BLOCK_SIZE) {
                    size_t i_end = (i0 + BLOCK_SIZE < rows) ? i0 + BLOCK_SIZE : rows;
                    size_t j_end = (j0 + BLOCK_SIZE < cols) ? j0 + BLOCK_SIZE : cols;
                    for (size_t i = i0; i < i_end; i++) {
                        for (size_t j = j0; j < j_end; j++) {
                            d[j * rows + i] = s[i * cols + j];
                        }
                    }
                }
            }
            break;
        }
        case DTYPE_F32: {
            float* d = (float*)byte_array_ptr(dst);
            const float* s = (const float*)byte_array_ptr(src);
            for (size_t i0 = 0; i0 < rows; i0 += BLOCK_SIZE) {
                for (size_t j0 = 0; j0 < cols; j0 += BLOCK_SIZE) {
                    size_t i_end = (i0 + BLOCK_SIZE < rows) ? i0 + BLOCK_SIZE : rows;
                    size_t j_end = (j0 + BLOCK_SIZE < cols) ? j0 + BLOCK_SIZE : cols;
                    for (size_t i = i0; i < i_end; i++) {
                        for (size_t j = j0; j < j_end; j++) {
                            d[j * rows + i] = s[i * cols + j];
                        }
                    }
                }
            }
            break;
        }
        default: break;
    }
    return dst;
}

/* General axis permutation - more complex, handle arbitrary dimensions */
LEAN_EXPORT lean_obj_res k_permute(lean_obj_arg dst, b_lean_obj_arg src,
                                    size_t ndim, b_lean_obj_arg shape_arr,
                                    b_lean_obj_arg perm_arr, uint8_t dt) {
    dst = ensure_exclusive(dst);

    /* For now, just handle the common cases inline */
    /* Full implementation would need stride calculation */

    const size_t* shape = (const size_t*)byte_array_ptr(shape_arr);
    const size_t* perm = (const size_t*)byte_array_ptr(perm_arr);

    /* Calculate total elements and strides */
    size_t total = 1;
    for (size_t i = 0; i < ndim; i++) total *= shape[i];

    /* Compute source strides (row-major) */
    size_t* src_strides = (size_t*)alloca(ndim * sizeof(size_t));
    src_strides[ndim - 1] = 1;
    for (size_t i = ndim - 1; i > 0; i--) {
        src_strides[i - 1] = src_strides[i] * shape[i];
    }

    /* Compute destination shape and strides */
    size_t* dst_shape = (size_t*)alloca(ndim * sizeof(size_t));
    size_t* dst_strides = (size_t*)alloca(ndim * sizeof(size_t));
    for (size_t i = 0; i < ndim; i++) {
        dst_shape[i] = shape[perm[i]];
    }
    dst_strides[ndim - 1] = 1;
    for (size_t i = ndim - 1; i > 0; i--) {
        dst_strides[i - 1] = dst_strides[i] * dst_shape[i];
    }

    /* Permute elements */
    size_t elem_size = dtype_size((DType)dt);
    uint8_t* d = (uint8_t*)byte_array_ptr(dst);
    const uint8_t* s = (const uint8_t*)byte_array_ptr(src);

    size_t* idx = (size_t*)alloca(ndim * sizeof(size_t));
    memset(idx, 0, ndim * sizeof(size_t));

    for (size_t flat = 0; flat < total; flat++) {
        /* Compute source linear index */
        size_t src_idx = 0;
        for (size_t i = 0; i < ndim; i++) {
            src_idx += idx[i] * src_strides[i];
        }

        /* Compute destination linear index (permuted) */
        size_t dst_idx = 0;
        for (size_t i = 0; i < ndim; i++) {
            dst_idx += idx[perm[i]] * dst_strides[i];
        }

        /* Copy element */
        memcpy(d + dst_idx * elem_size, s + src_idx * elem_size, elem_size);

        /* Increment multi-index */
        for (size_t i = ndim; i > 0; i--) {
            idx[i - 1]++;
            if (idx[i - 1] < shape[i - 1]) break;
            idx[i - 1] = 0;
        }
    }

    return dst;
}

/* ============================================================================
 * Tier 7: Random Number Generation
 * Using xoshiro256** for quality + speed
 * ============================================================================ */

static uint64_t rng_state[4] = {
    0x853c49e6748fea9bULL,
    0xda3e39cb94b95bdbULL,
    0x7e46e4d7c5f3b298ULL,
    0x1a2b3c4d5e6f7a8bULL
};

static inline uint64_t rotl(const uint64_t x, int k) {
    return (x << k) | (x >> (64 - k));
}

static inline uint64_t xoshiro256ss_next(void) {
    const uint64_t result = rotl(rng_state[1] * 5, 7) * 9;
    const uint64_t t = rng_state[1] << 17;
    rng_state[2] ^= rng_state[0];
    rng_state[3] ^= rng_state[1];
    rng_state[1] ^= rng_state[2];
    rng_state[0] ^= rng_state[3];
    rng_state[2] ^= t;
    rng_state[3] = rotl(rng_state[3], 45);
    return result;
}

LEAN_EXPORT void k_rng_seed(uint64_t seed) {
    /* SplitMix64 to initialize state from single seed */
    for (int i = 0; i < 4; i++) {
        seed += 0x9e3779b97f4a7c15ULL;
        uint64_t z = seed;
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
        z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
        rng_state[i] = z ^ (z >> 31);
    }
}

/* Convert uint64 to uniform [0, 1) */
static inline double u64_to_uniform(uint64_t x) {
    return (x >> 11) * 0x1.0p-53;
}

/* Box-Muller for normal distribution */
static inline void box_muller(double* out1, double* out2) {
    double u1 = u64_to_uniform(xoshiro256ss_next());
    double u2 = u64_to_uniform(xoshiro256ss_next());
    /* Avoid log(0) */
    while (u1 == 0.0) u1 = u64_to_uniform(xoshiro256ss_next());
    double mag = sqrt(-2.0 * log(u1));
    double angle = 2.0 * M_PI * u2;
    *out1 = mag * cos(angle);
    *out2 = mag * sin(angle);
}

LEAN_EXPORT lean_obj_res k_rand_uniform(lean_obj_arg dst, size_t n, uint8_t dt) {
    dst = ensure_exclusive(dst);
    switch ((DType)dt) {
        case DTYPE_F64: {
            double* d = (double*)byte_array_ptr(dst);
            for (size_t i = 0; i < n; i++) {
                d[i] = u64_to_uniform(xoshiro256ss_next());
            }
            break;
        }
        case DTYPE_F32: {
            float* d = (float*)byte_array_ptr(dst);
            for (size_t i = 0; i < n; i++) {
                d[i] = (float)u64_to_uniform(xoshiro256ss_next());
            }
            break;
        }
        default: break;
    }
    return dst;
}

LEAN_EXPORT lean_obj_res k_rand_normal(lean_obj_arg dst, size_t n, uint8_t dt) {
    dst = ensure_exclusive(dst);
    switch ((DType)dt) {
        case DTYPE_F64: {
            double* d = (double*)byte_array_ptr(dst);
            size_t i = 0;
            while (i + 1 < n) {
                box_muller(&d[i], &d[i + 1]);
                i += 2;
            }
            if (i < n) {
                double tmp;
                box_muller(&d[i], &tmp);
            }
            break;
        }
        case DTYPE_F32: {
            float* d = (float*)byte_array_ptr(dst);
            size_t i = 0;
            while (i + 1 < n) {
                double n1, n2;
                box_muller(&n1, &n2);
                d[i] = (float)n1;
                d[i + 1] = (float)n2;
                i += 2;
            }
            if (i < n) {
                double n1, tmp;
                box_muller(&n1, &tmp);
                d[i] = (float)n1;
            }
            break;
        }
        default: break;
    }
    return dst;
}
