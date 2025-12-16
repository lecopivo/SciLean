/*
 * SciLean Kernel - Dtype-parametric tensor operations
 *
 * Implements: f64, f32, bf16, fp8 (e4m3, e5m2)
 * TODO: f16, int types
 *
 * Optimization notes (patterns for future codegen):
 * - TILE_M/N/K: Cache blocking parameters (tune per architecture)
 * - SIMD width: 4 for NEON float32, 8 for AVX256, 16 for AVX512
 * - Unroll factor: Balance register pressure vs loop overhead
 */

#include "kernel.h"
#include <math.h>
#include <string.h>
#include <stdlib.h>

/* SIMD support - detect architecture */
#if defined(__ARM_NEON) || defined(__ARM_NEON__)
  #include <arm_neon.h>
  #define HAVE_NEON 1
#elif defined(__AVX2__)
  #include <immintrin.h>
  #define HAVE_AVX2 1
#elif defined(__SSE4_1__)
  #include <smmintrin.h>
  #define HAVE_SSE4 1
#endif

/* Cache blocking parameters - tuned for L1/L2 cache sizes on Apple Silicon */
#define TILE_M 128
#define TILE_N 128
#define TILE_K 128

/* ============================================================================
 * BFloat16 and FP8 Conversion Functions
 *
 * BFloat16: 1 sign + 8 exponent + 7 mantissa (same exponent as f32)
 * FP8 E4M3: 1 sign + 4 exponent + 3 mantissa (ML inference)
 * FP8 E5M2: 1 sign + 5 exponent + 2 mantissa (ML training)
 * ============================================================================ */

typedef uint16_t bf16_t;
typedef uint8_t fp8_t;

/* BFloat16 to Float32 - simple shift since exponent bits match */
static inline float bf16_to_f32(bf16_t x) {
    uint32_t bits = (uint32_t)x << 16;
    float f;
    memcpy(&f, &bits, sizeof(f));
    return f;
}

/* Float32 to BFloat16 - truncate mantissa (could add rounding) */
static inline bf16_t f32_to_bf16(float f) {
    uint32_t bits;
    memcpy(&bits, &f, sizeof(bits));
    /* Simple truncation - for better accuracy, add round-to-nearest-even */
    return (bf16_t)(bits >> 16);
}

/* FP8 E4M3 to Float32
 * E4M3: bias=7, max exponent=15 (special: 15 with mantissa!=0 is NaN)
 * Range: ±448 (no infinities, only NaNs at exp=15, mant!=0)
 */
static inline float fp8_e4m3_to_f32(fp8_t x) {
    uint8_t sign = (x >> 7) & 1;
    uint8_t exp = (x >> 3) & 0xF;
    uint8_t mant = x & 0x7;

    if (exp == 0) {
        /* Subnormal or zero */
        if (mant == 0) return sign ? -0.0f : 0.0f;
        /* Subnormal: value = (-1)^sign * 2^(-6) * (mant/8) */
        float val = ldexpf((float)mant / 8.0f, -6);
        return sign ? -val : val;
    } else if (exp == 15 && mant != 0) {
        /* NaN */
        return NAN;
    } else {
        /* Normal: value = (-1)^sign * 2^(exp-7) * (1 + mant/8) */
        float val = ldexpf(1.0f + (float)mant / 8.0f, exp - 7);
        return sign ? -val : val;
    }
}

/* Float32 to FP8 E4M3 */
static inline fp8_t f32_to_fp8_e4m3(float f) {
    if (isnan(f)) return 0x7F; /* NaN representation */
    if (f == 0.0f) return 0;
    if (f == -0.0f) return 0x80;

    uint32_t bits;
    memcpy(&bits, &f, sizeof(bits));
    uint8_t sign = (bits >> 31) & 1;
    int32_t exp = ((bits >> 23) & 0xFF) - 127;  /* Unbias f32 exponent */
    uint32_t mant = bits & 0x7FFFFF;

    /* Rebias to E4M3 (bias=7) and clamp */
    int32_t new_exp = exp + 7;

    if (new_exp >= 15) {
        /* Overflow to max (no inf in E4M3) */
        return (sign << 7) | 0x7E; /* Max normal: exp=14, mant=6 gives ±448 */
    } else if (new_exp <= 0) {
        /* Underflow to subnormal or zero */
        if (new_exp < -3) return sign << 7; /* Zero */
        /* Subnormal */
        uint8_t mant3 = (uint8_t)((mant >> 20) | 0x8) >> (1 - new_exp);
        return (sign << 7) | (mant3 & 0x7);
    } else {
        /* Normal */
        uint8_t mant3 = (uint8_t)(mant >> 20) & 0x7;
        return (sign << 7) | (new_exp << 3) | mant3;
    }
}

/* FP8 E5M2 to Float32
 * E5M2: bias=15, has infinities and NaNs like IEEE
 */
static inline float fp8_e5m2_to_f32(fp8_t x) {
    uint8_t sign = (x >> 7) & 1;
    uint8_t exp = (x >> 2) & 0x1F;
    uint8_t mant = x & 0x3;

    if (exp == 0) {
        /* Subnormal or zero */
        if (mant == 0) return sign ? -0.0f : 0.0f;
        float val = ldexpf((float)mant / 4.0f, -14);
        return sign ? -val : val;
    } else if (exp == 31) {
        /* Inf or NaN */
        if (mant == 0) return sign ? -INFINITY : INFINITY;
        return NAN;
    } else {
        /* Normal */
        float val = ldexpf(1.0f + (float)mant / 4.0f, exp - 15);
        return sign ? -val : val;
    }
}

/* Float32 to FP8 E5M2 */
static inline fp8_t f32_to_fp8_e5m2(float f) {
    if (isnan(f)) return 0x7F; /* NaN */
    if (isinf(f)) return (f < 0) ? 0xFC : 0x7C; /* ±Inf */
    if (f == 0.0f) return 0;
    if (f == -0.0f) return 0x80;

    uint32_t bits;
    memcpy(&bits, &f, sizeof(bits));
    uint8_t sign = (bits >> 31) & 1;
    int32_t exp = ((bits >> 23) & 0xFF) - 127;
    uint32_t mant = bits & 0x7FFFFF;

    /* Rebias to E5M2 (bias=15) */
    int32_t new_exp = exp + 15;

    if (new_exp >= 31) {
        /* Overflow to inf */
        return (sign << 7) | 0x7C;
    } else if (new_exp <= 0) {
        /* Underflow */
        if (new_exp < -2) return sign << 7;
        uint8_t mant2 = (uint8_t)((mant >> 21) | 0x4) >> (1 - new_exp);
        return (sign << 7) | (mant2 & 0x3);
    } else {
        uint8_t mant2 = (uint8_t)(mant >> 21) & 0x3;
        return (sign << 7) | (new_exp << 2) | mant2;
    }
}

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
        case DTYPE_BF16: {                                                      \
            bf16_t* d = (bf16_t*)byte_array_ptr(dst);                           \
            const bf16_t* pa = (const bf16_t*)byte_array_ptr(a);                \
            const bf16_t* pb = (const bf16_t*)byte_array_ptr(b);                \
            for (size_t i = 0; i < n; i++) {                                    \
                float va = bf16_to_f32(pa[i]), vb = bf16_to_f32(pb[i]);         \
                d[i] = f32_to_bf16(va op vb);                                   \
            }                                                                   \
            break;                                                              \
        }                                                                       \
        case DTYPE_F8_E4M3: {                                                   \
            fp8_t* d = (fp8_t*)byte_array_ptr(dst);                             \
            const fp8_t* pa = (const fp8_t*)byte_array_ptr(a);                  \
            const fp8_t* pb = (const fp8_t*)byte_array_ptr(b);                  \
            for (size_t i = 0; i < n; i++) {                                    \
                float va = fp8_e4m3_to_f32(pa[i]), vb = fp8_e4m3_to_f32(pb[i]); \
                d[i] = f32_to_fp8_e4m3(va op vb);                               \
            }                                                                   \
            break;                                                              \
        }                                                                       \
        case DTYPE_F8_E5M2: {                                                   \
            fp8_t* d = (fp8_t*)byte_array_ptr(dst);                             \
            const fp8_t* pa = (const fp8_t*)byte_array_ptr(a);                  \
            const fp8_t* pb = (const fp8_t*)byte_array_ptr(b);                  \
            for (size_t i = 0; i < n; i++) {                                    \
                float va = fp8_e5m2_to_f32(pa[i]), vb = fp8_e5m2_to_f32(pb[i]); \
                d[i] = f32_to_fp8_e5m2(va op vb);                               \
            }                                                                   \
            break;                                                              \
        }                                                                       \
        default: break;                                                         \
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
        case DTYPE_BF16: {
            bf16_t* d = (bf16_t*)byte_array_ptr(dst);
            const bf16_t* px = (const bf16_t*)byte_array_ptr(x);
            for (size_t i = 0; i < n; i++) d[i] = px[i] ^ 0x8000; /* Flip sign bit */
            break;
        }
        case DTYPE_F8_E4M3:
        case DTYPE_F8_E5M2: {
            fp8_t* d = (fp8_t*)byte_array_ptr(dst);
            const fp8_t* px = (const fp8_t*)byte_array_ptr(x);
            for (size_t i = 0; i < n; i++) d[i] = px[i] ^ 0x80; /* Flip sign bit */
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
        case DTYPE_BF16: {
            bf16_t* d = (bf16_t*)byte_array_ptr(dst);
            const bf16_t* px = (const bf16_t*)byte_array_ptr(x);
            for (size_t i = 0; i < n; i++) d[i] = px[i] & 0x7FFF; /* Clear sign bit */
            break;
        }
        case DTYPE_F8_E4M3:
        case DTYPE_F8_E5M2: {
            fp8_t* d = (fp8_t*)byte_array_ptr(dst);
            const fp8_t* px = (const fp8_t*)byte_array_ptr(x);
            for (size_t i = 0; i < n; i++) d[i] = px[i] & 0x7F; /* Clear sign bit */
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
        case DTYPE_BF16: {                                                      \
            bf16_t* d = (bf16_t*)byte_array_ptr(dst);                           \
            const bf16_t* px = (const bf16_t*)byte_array_ptr(x);                \
            for (size_t i = 0; i < n; i++) {                                    \
                d[i] = f32_to_bf16(f32_fn(bf16_to_f32(px[i])));                 \
            }                                                                   \
            break;                                                              \
        }                                                                       \
        case DTYPE_F8_E4M3: {                                                   \
            fp8_t* d = (fp8_t*)byte_array_ptr(dst);                             \
            const fp8_t* px = (const fp8_t*)byte_array_ptr(x);                  \
            for (size_t i = 0; i < n; i++) {                                    \
                d[i] = f32_to_fp8_e4m3(f32_fn(fp8_e4m3_to_f32(px[i])));         \
            }                                                                   \
            break;                                                              \
        }                                                                       \
        case DTYPE_F8_E5M2: {                                                   \
            fp8_t* d = (fp8_t*)byte_array_ptr(dst);                             \
            const fp8_t* px = (const fp8_t*)byte_array_ptr(x);                  \
            for (size_t i = 0; i < n; i++) {                                    \
                d[i] = f32_to_fp8_e5m2(f32_fn(fp8_e5m2_to_f32(px[i])));         \
            }                                                                   \
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
        case DTYPE_BF16: {
            const bf16_t* px = (const bf16_t*)byte_array_ptr(x);
            for (size_t i = 0; i < n; i++) sum += (double)bf16_to_f32(px[i]);
            break;
        }
        case DTYPE_F8_E4M3: {
            const fp8_t* px = (const fp8_t*)byte_array_ptr(x);
            for (size_t i = 0; i < n; i++) sum += (double)fp8_e4m3_to_f32(px[i]);
            break;
        }
        case DTYPE_F8_E5M2: {
            const fp8_t* px = (const fp8_t*)byte_array_ptr(x);
            for (size_t i = 0; i < n; i++) sum += (double)fp8_e5m2_to_f32(px[i]);
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
        case DTYPE_BF16: {
            const bf16_t* px = (const bf16_t*)byte_array_ptr(x);
            max_val = (double)bf16_to_f32(px[0]);
            for (size_t i = 1; i < n; i++) {
                float v = bf16_to_f32(px[i]);
                if (v > max_val) max_val = (double)v;
            }
            break;
        }
        case DTYPE_F8_E4M3: {
            const fp8_t* px = (const fp8_t*)byte_array_ptr(x);
            max_val = (double)fp8_e4m3_to_f32(px[0]);
            for (size_t i = 1; i < n; i++) {
                float v = fp8_e4m3_to_f32(px[i]);
                if (v > max_val) max_val = (double)v;
            }
            break;
        }
        case DTYPE_F8_E5M2: {
            const fp8_t* px = (const fp8_t*)byte_array_ptr(x);
            max_val = (double)fp8_e5m2_to_f32(px[0]);
            for (size_t i = 1; i < n; i++) {
                float v = fp8_e5m2_to_f32(px[i]);
                if (v > max_val) max_val = (double)v;
            }
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
        case DTYPE_BF16: {
            const bf16_t* px = (const bf16_t*)byte_array_ptr(x);
            float max_val = bf16_to_f32(px[0]);
            for (size_t i = 1; i < n; i++) {
                float v = bf16_to_f32(px[i]);
                if (v > max_val) { max_val = v; max_idx = i; }
            }
            break;
        }
        case DTYPE_F8_E4M3: {
            const fp8_t* px = (const fp8_t*)byte_array_ptr(x);
            float max_val = fp8_e4m3_to_f32(px[0]);
            for (size_t i = 1; i < n; i++) {
                float v = fp8_e4m3_to_f32(px[i]);
                if (v > max_val) { max_val = v; max_idx = i; }
            }
            break;
        }
        case DTYPE_F8_E5M2: {
            const fp8_t* px = (const fp8_t*)byte_array_ptr(x);
            float max_val = fp8_e5m2_to_f32(px[0]);
            for (size_t i = 1; i < n; i++) {
                float v = fp8_e5m2_to_f32(px[i]);
                if (v > max_val) { max_val = v; max_idx = i; }
            }
            break;
        }
        default: break;
    }
    return max_idx;
}

/* ============================================================================
 * Tier 4: Contractions - Optimized GEMM
 *
 * Strategy (patterns for codegen):
 * 1. Tile outer loops by TILE_M × TILE_N to fit in L2 cache
 * 2. Tile inner loop by TILE_K to fit A tile + B tile in L1
 * 3. Micro-kernel: SIMD vectorized, unrolled accumulation
 * 4. Edge handling: Scalar fallback for remainder
 * ============================================================================ */

#ifdef HAVE_NEON
/* NEON micro-kernel: 8×8 block of C += A_panel × B_panel
 * K-unroll=4 for instruction-level parallelism (~95-100 GFLOP/s on Apple Silicon)
 * Generated by codegen/GemmGen.lean */
__attribute__((always_inline))
static inline void gemm_microkernel_8x8_k4_neon(
    float* __restrict__ C, size_t ldc,
    const float* __restrict__ A, size_t lda,
    const float* __restrict__ B, size_t ldb,
    size_t K)
{
    /* 8×8 accumulator in registers (64 floats = 16 NEON vectors) */
    float32x4_t c0_0 = vdupq_n_f32(0.0f);
    float32x4_t c0_1 = vdupq_n_f32(0.0f);
    float32x4_t c1_0 = vdupq_n_f32(0.0f);
    float32x4_t c1_1 = vdupq_n_f32(0.0f);
    float32x4_t c2_0 = vdupq_n_f32(0.0f);
    float32x4_t c2_1 = vdupq_n_f32(0.0f);
    float32x4_t c3_0 = vdupq_n_f32(0.0f);
    float32x4_t c3_1 = vdupq_n_f32(0.0f);
    float32x4_t c4_0 = vdupq_n_f32(0.0f);
    float32x4_t c4_1 = vdupq_n_f32(0.0f);
    float32x4_t c5_0 = vdupq_n_f32(0.0f);
    float32x4_t c5_1 = vdupq_n_f32(0.0f);
    float32x4_t c6_0 = vdupq_n_f32(0.0f);
    float32x4_t c6_1 = vdupq_n_f32(0.0f);
    float32x4_t c7_0 = vdupq_n_f32(0.0f);
    float32x4_t c7_1 = vdupq_n_f32(0.0f);

    size_t kk = 0;
    /* K-unrolled main loop (unroll=4) */
    for (; kk + 4 <= K; kk += 4) {
        /* Unroll 0 */
        float32x4_t a0_u0 = {A[0*lda + (kk + 0)], A[1*lda + (kk + 0)], A[2*lda + (kk + 0)], A[3*lda + (kk + 0)]};
        float32x4_t a1_u0 = {A[4*lda + (kk + 0)], A[5*lda + (kk + 0)], A[6*lda + (kk + 0)], A[7*lda + (kk + 0)]};
        float32x4_t b0_u0 = vld1q_f32(&B[(kk + 0) * ldb + 0]);
        float32x4_t b1_u0 = vld1q_f32(&B[(kk + 0) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u0, a0_u0, 0);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u0, a0_u0, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u0, a0_u0, 1);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u0, a0_u0, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u0, a0_u0, 2);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u0, a0_u0, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u0, a0_u0, 3);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u0, a0_u0, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u0, a1_u0, 0);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u0, a1_u0, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u0, a1_u0, 1);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u0, a1_u0, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u0, a1_u0, 2);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u0, a1_u0, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u0, a1_u0, 3);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u0, a1_u0, 3);

        /* Unroll 1 */
        float32x4_t a0_u1 = {A[0*lda + (kk + 1)], A[1*lda + (kk + 1)], A[2*lda + (kk + 1)], A[3*lda + (kk + 1)]};
        float32x4_t a1_u1 = {A[4*lda + (kk + 1)], A[5*lda + (kk + 1)], A[6*lda + (kk + 1)], A[7*lda + (kk + 1)]};
        float32x4_t b0_u1 = vld1q_f32(&B[(kk + 1) * ldb + 0]);
        float32x4_t b1_u1 = vld1q_f32(&B[(kk + 1) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u1, a0_u1, 0);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u1, a0_u1, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u1, a0_u1, 1);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u1, a0_u1, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u1, a0_u1, 2);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u1, a0_u1, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u1, a0_u1, 3);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u1, a0_u1, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u1, a1_u1, 0);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u1, a1_u1, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u1, a1_u1, 1);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u1, a1_u1, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u1, a1_u1, 2);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u1, a1_u1, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u1, a1_u1, 3);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u1, a1_u1, 3);

        /* Unroll 2 */
        float32x4_t a0_u2 = {A[0*lda + (kk + 2)], A[1*lda + (kk + 2)], A[2*lda + (kk + 2)], A[3*lda + (kk + 2)]};
        float32x4_t a1_u2 = {A[4*lda + (kk + 2)], A[5*lda + (kk + 2)], A[6*lda + (kk + 2)], A[7*lda + (kk + 2)]};
        float32x4_t b0_u2 = vld1q_f32(&B[(kk + 2) * ldb + 0]);
        float32x4_t b1_u2 = vld1q_f32(&B[(kk + 2) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u2, a0_u2, 0);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u2, a0_u2, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u2, a0_u2, 1);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u2, a0_u2, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u2, a0_u2, 2);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u2, a0_u2, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u2, a0_u2, 3);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u2, a0_u2, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u2, a1_u2, 0);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u2, a1_u2, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u2, a1_u2, 1);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u2, a1_u2, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u2, a1_u2, 2);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u2, a1_u2, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u2, a1_u2, 3);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u2, a1_u2, 3);

        /* Unroll 3 */
        float32x4_t a0_u3 = {A[0*lda + (kk + 3)], A[1*lda + (kk + 3)], A[2*lda + (kk + 3)], A[3*lda + (kk + 3)]};
        float32x4_t a1_u3 = {A[4*lda + (kk + 3)], A[5*lda + (kk + 3)], A[6*lda + (kk + 3)], A[7*lda + (kk + 3)]};
        float32x4_t b0_u3 = vld1q_f32(&B[(kk + 3) * ldb + 0]);
        float32x4_t b1_u3 = vld1q_f32(&B[(kk + 3) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u3, a0_u3, 0);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u3, a0_u3, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u3, a0_u3, 1);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u3, a0_u3, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u3, a0_u3, 2);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u3, a0_u3, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u3, a0_u3, 3);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u3, a0_u3, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u3, a1_u3, 0);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u3, a1_u3, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u3, a1_u3, 1);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u3, a1_u3, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u3, a1_u3, 2);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u3, a1_u3, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u3, a1_u3, 3);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u3, a1_u3, 3);
    }
    /* Remainder loop */
    for (; kk < K; kk++) {
        float32x4_t a0_r = {A[0*lda + (kk)], A[1*lda + (kk)], A[2*lda + (kk)], A[3*lda + (kk)]};
        float32x4_t a1_r = {A[4*lda + (kk)], A[5*lda + (kk)], A[6*lda + (kk)], A[7*lda + (kk)]};
        float32x4_t b0_r = vld1q_f32(&B[(kk) * ldb + 0]);
        float32x4_t b1_r = vld1q_f32(&B[(kk) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_r, a0_r, 0);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_r, a0_r, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_r, a0_r, 1);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_r, a0_r, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_r, a0_r, 2);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_r, a0_r, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_r, a0_r, 3);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_r, a0_r, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_r, a1_r, 0);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_r, a1_r, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_r, a1_r, 1);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_r, a1_r, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_r, a1_r, 2);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_r, a1_r, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_r, a1_r, 3);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_r, a1_r, 3);
    }

    /* Store back to C */
    vst1q_f32(&C[0*ldc + 0], vaddq_f32(vld1q_f32(&C[0*ldc + 0]), c0_0));
    vst1q_f32(&C[0*ldc + 4], vaddq_f32(vld1q_f32(&C[0*ldc + 4]), c0_1));
    vst1q_f32(&C[1*ldc + 0], vaddq_f32(vld1q_f32(&C[1*ldc + 0]), c1_0));
    vst1q_f32(&C[1*ldc + 4], vaddq_f32(vld1q_f32(&C[1*ldc + 4]), c1_1));
    vst1q_f32(&C[2*ldc + 0], vaddq_f32(vld1q_f32(&C[2*ldc + 0]), c2_0));
    vst1q_f32(&C[2*ldc + 4], vaddq_f32(vld1q_f32(&C[2*ldc + 4]), c2_1));
    vst1q_f32(&C[3*ldc + 0], vaddq_f32(vld1q_f32(&C[3*ldc + 0]), c3_0));
    vst1q_f32(&C[3*ldc + 4], vaddq_f32(vld1q_f32(&C[3*ldc + 4]), c3_1));
    vst1q_f32(&C[4*ldc + 0], vaddq_f32(vld1q_f32(&C[4*ldc + 0]), c4_0));
    vst1q_f32(&C[4*ldc + 4], vaddq_f32(vld1q_f32(&C[4*ldc + 4]), c4_1));
    vst1q_f32(&C[5*ldc + 0], vaddq_f32(vld1q_f32(&C[5*ldc + 0]), c5_0));
    vst1q_f32(&C[5*ldc + 4], vaddq_f32(vld1q_f32(&C[5*ldc + 4]), c5_1));
    vst1q_f32(&C[6*ldc + 0], vaddq_f32(vld1q_f32(&C[6*ldc + 0]), c6_0));
    vst1q_f32(&C[6*ldc + 4], vaddq_f32(vld1q_f32(&C[6*ldc + 4]), c6_1));
    vst1q_f32(&C[7*ldc + 0], vaddq_f32(vld1q_f32(&C[7*ldc + 0]), c7_0));
    vst1q_f32(&C[7*ldc + 4], vaddq_f32(vld1q_f32(&C[7*ldc + 4]), c7_1));
}

/* Tiled GEMM for f32 using NEON with 8×8 micro-kernel */
__attribute__((always_inline))
static inline void gemm_f32_tiled_neon(
    float* __restrict__ C,
    const float* __restrict__ A,
    const float* __restrict__ B,
    size_t M, size_t K, size_t N,
    float alpha, float beta)
{
    /* Apply beta to C first */
    if (beta != 1.0f) {
        for (size_t i = 0; i < M * N; i++) {
            C[i] *= beta;
        }
    }

    /* Tile over M, N, K */
    for (size_t i0 = 0; i0 < M; i0 += TILE_M) {
        size_t i_end = (i0 + TILE_M < M) ? i0 + TILE_M : M;

        for (size_t j0 = 0; j0 < N; j0 += TILE_N) {
            size_t j_end = (j0 + TILE_N < N) ? j0 + TILE_N : N;

            for (size_t k0 = 0; k0 < K; k0 += TILE_K) {
                size_t k_end = (k0 + TILE_K < K) ? k0 + TILE_K : K;
                size_t tile_k = k_end - k0;

                /* Process 8×8 micro-tiles within this tile */
                size_t i;
                for (i = i0; i + 8 <= i_end; i += 8) {
                    size_t j;
                    for (j = j0; j + 8 <= j_end; j += 8) {
                        gemm_microkernel_8x8_k4_neon(
                            &C[i * N + j], N,
                            &A[i * K + k0], K,
                            &B[k0 * N + j], N,
                            tile_k);
                    }
                    /* Handle remaining columns (< 8) */
                    for (; j < j_end; j++) {
                        for (size_t ii = i; ii < i + 8; ii++) {
                            float sum = 0.0f;
                            for (size_t kk = k0; kk < k_end; kk++) {
                                sum += A[ii * K + kk] * B[kk * N + j];
                            }
                            C[ii * N + j] += sum;
                        }
                    }
                }
                /* Handle remaining rows (< 8) */
                for (; i < i_end; i++) {
                    for (size_t j = j0; j < j_end; j++) {
                        float sum = 0.0f;
                        for (size_t kk = k0; kk < k_end; kk++) {
                            sum += A[i * K + kk] * B[kk * N + j];
                        }
                        C[i * N + j] += sum;
                    }
                }
            }
        }
    }

    /* Apply alpha if needed */
    if (alpha != 1.0f) {
        for (size_t i = 0; i < M * N; i++) {
            C[i] *= alpha;
        }
    }
}
#endif /* HAVE_NEON */

/* Scalar tiled GEMM - fallback for any architecture */
__attribute__((always_inline))
static inline void gemm_f32_tiled_scalar(
    float* __restrict__ C,
    const float* __restrict__ A,
    const float* __restrict__ B,
    size_t M, size_t K, size_t N,
    float alpha, float beta)
{
    /* Apply beta */
    for (size_t i = 0; i < M * N; i++) {
        C[i] *= beta;
    }

    /* Tiled multiply-accumulate */
    for (size_t i0 = 0; i0 < M; i0 += TILE_M) {
        size_t i_end = (i0 + TILE_M < M) ? i0 + TILE_M : M;
        for (size_t j0 = 0; j0 < N; j0 += TILE_N) {
            size_t j_end = (j0 + TILE_N < N) ? j0 + TILE_N : N;
            for (size_t k0 = 0; k0 < K; k0 += TILE_K) {
                size_t k_end = (k0 + TILE_K < K) ? k0 + TILE_K : K;

                /* Micro-tile: accumulate into C[i,j] */
                for (size_t i = i0; i < i_end; i++) {
                    for (size_t j = j0; j < j_end; j++) {
                        float sum = 0.0f;
                        for (size_t k = k0; k < k_end; k++) {
                            sum += A[i * K + k] * B[k * N + j];
                        }
                        C[i * N + j] += sum;
                    }
                }
            }
        }
    }

    /* Apply alpha */
    if (alpha != 1.0f) {
        for (size_t i = 0; i < M * N; i++) {
            C[i] *= alpha;
        }
    }
}

/* GEMM: C[m,n] = alpha * A[m,k] @ B[k,n] + beta * C[m,n]
 * Row-major layout.
 * bf16/fp8: accumulate in f32 for numerical stability, then convert back. */
LEAN_EXPORT lean_obj_res k_gemm(lean_obj_arg C, b_lean_obj_arg A, b_lean_obj_arg B,
                                 size_t m, size_t k, size_t n,
                                 double alpha, double beta, uint8_t dt) {
    C = ensure_exclusive(C);
    switch ((DType)dt) {
        case DTYPE_F64: {
            double* pc = (double*)byte_array_ptr(C);
            const double* pa = (const double*)byte_array_ptr(A);
            const double* pb = (const double*)byte_array_ptr(B);
            /* Initialize C with beta scaling */
            if (beta == 0.0) {
                for (size_t i = 0; i < m * n; i++) pc[i] = 0.0;
            } else if (beta != 1.0) {
                for (size_t i = 0; i < m * n; i++) pc[i] *= beta;
            }
            /* ikj loop order for cache-friendly B access */
            for (size_t i = 0; i < m; i++) {
                for (size_t l = 0; l < k; l++) {
                    double a_il = alpha * pa[i * k + l];
                    for (size_t j = 0; j < n; j++) {
                        pc[i * n + j] += a_il * pb[l * n + j];
                    }
                }
            }
            break;
        }
        case DTYPE_F32: {
            float* pc = (float*)byte_array_ptr(C);
            const float* pa = (const float*)byte_array_ptr(A);
            const float* pb = (const float*)byte_array_ptr(B);
#ifdef HAVE_NEON
            gemm_f32_tiled_neon(pc, pa, pb, m, k, n, (float)alpha, (float)beta);
#else
            gemm_f32_tiled_scalar(pc, pa, pb, m, k, n, (float)alpha, (float)beta);
#endif
            break;
        }
        case DTYPE_BF16: {
            bf16_t* pc = (bf16_t*)byte_array_ptr(C);
            const bf16_t* pa = (const bf16_t*)byte_array_ptr(A);
            const bf16_t* pb = (const bf16_t*)byte_array_ptr(B);
            float a = (float)alpha, b = (float)beta;
            for (size_t i = 0; i < m; i++) {
                for (size_t j = 0; j < n; j++) {
                    float sum = 0.0f;
                    for (size_t l = 0; l < k; l++) {
                        sum += bf16_to_f32(pa[i * k + l]) * bf16_to_f32(pb[l * n + j]);
                    }
                    float c_old = bf16_to_f32(pc[i * n + j]);
                    pc[i * n + j] = f32_to_bf16(a * sum + b * c_old);
                }
            }
            break;
        }
        case DTYPE_F8_E4M3: {
            fp8_t* pc = (fp8_t*)byte_array_ptr(C);
            const fp8_t* pa = (const fp8_t*)byte_array_ptr(A);
            const fp8_t* pb = (const fp8_t*)byte_array_ptr(B);
            float a = (float)alpha, b = (float)beta;
            for (size_t i = 0; i < m; i++) {
                for (size_t j = 0; j < n; j++) {
                    float sum = 0.0f;
                    for (size_t l = 0; l < k; l++) {
                        sum += fp8_e4m3_to_f32(pa[i * k + l]) * fp8_e4m3_to_f32(pb[l * n + j]);
                    }
                    float c_old = fp8_e4m3_to_f32(pc[i * n + j]);
                    pc[i * n + j] = f32_to_fp8_e4m3(a * sum + b * c_old);
                }
            }
            break;
        }
        case DTYPE_F8_E5M2: {
            fp8_t* pc = (fp8_t*)byte_array_ptr(C);
            const fp8_t* pa = (const fp8_t*)byte_array_ptr(A);
            const fp8_t* pb = (const fp8_t*)byte_array_ptr(B);
            float a = (float)alpha, b = (float)beta;
            for (size_t i = 0; i < m; i++) {
                for (size_t j = 0; j < n; j++) {
                    float sum = 0.0f;
                    for (size_t l = 0; l < k; l++) {
                        sum += fp8_e5m2_to_f32(pa[i * k + l]) * fp8_e5m2_to_f32(pb[l * n + j]);
                    }
                    float c_old = fp8_e5m2_to_f32(pc[i * n + j]);
                    pc[i * n + j] = f32_to_fp8_e5m2(a * sum + b * c_old);
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
        case DTYPE_BF16: {
            bf16_t* py = (bf16_t*)byte_array_ptr(y);
            const bf16_t* pa = (const bf16_t*)byte_array_ptr(A);
            const bf16_t* px = (const bf16_t*)byte_array_ptr(x);
            for (size_t i = 0; i < m; i++) {
                float sum = 0.0f;
                for (size_t j = 0; j < n; j++) {
                    sum += bf16_to_f32(pa[i * n + j]) * bf16_to_f32(px[j]);
                }
                py[i] = f32_to_bf16(sum);
            }
            break;
        }
        case DTYPE_F8_E4M3: {
            fp8_t* py = (fp8_t*)byte_array_ptr(y);
            const fp8_t* pa = (const fp8_t*)byte_array_ptr(A);
            const fp8_t* px = (const fp8_t*)byte_array_ptr(x);
            for (size_t i = 0; i < m; i++) {
                float sum = 0.0f;
                for (size_t j = 0; j < n; j++) {
                    sum += fp8_e4m3_to_f32(pa[i * n + j]) * fp8_e4m3_to_f32(px[j]);
                }
                py[i] = f32_to_fp8_e4m3(sum);
            }
            break;
        }
        case DTYPE_F8_E5M2: {
            fp8_t* py = (fp8_t*)byte_array_ptr(y);
            const fp8_t* pa = (const fp8_t*)byte_array_ptr(A);
            const fp8_t* px = (const fp8_t*)byte_array_ptr(x);
            for (size_t i = 0; i < m; i++) {
                float sum = 0.0f;
                for (size_t j = 0; j < n; j++) {
                    sum += fp8_e5m2_to_f32(pa[i * n + j]) * fp8_e5m2_to_f32(px[j]);
                }
                py[i] = f32_to_fp8_e5m2(sum);
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

/* Numerically stable softmax
 * For bf16/fp8: compute in f32 for stability, convert back at the end */
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
        case DTYPE_BF16: {
            bf16_t* d = (bf16_t*)byte_array_ptr(dst);
            const bf16_t* px = (const bf16_t*)byte_array_ptr(x);
            /* Compute in f32 for numerical stability */
            float max_val = bf16_to_f32(px[0]);
            for (size_t i = 1; i < n; i++) {
                float v = bf16_to_f32(px[i]);
                if (v > max_val) max_val = v;
            }
            float sum = 0.0f;
            for (size_t i = 0; i < n; i++) {
                float e = expf(bf16_to_f32(px[i]) - max_val);
                d[i] = f32_to_bf16(e);  /* Store intermediate for memory */
                sum += e;
            }
            for (size_t i = 0; i < n; i++) {
                d[i] = f32_to_bf16(bf16_to_f32(d[i]) / sum);
            }
            break;
        }
        case DTYPE_F8_E4M3: {
            fp8_t* d = (fp8_t*)byte_array_ptr(dst);
            const fp8_t* px = (const fp8_t*)byte_array_ptr(x);
            float max_val = fp8_e4m3_to_f32(px[0]);
            for (size_t i = 1; i < n; i++) {
                float v = fp8_e4m3_to_f32(px[i]);
                if (v > max_val) max_val = v;
            }
            float sum = 0.0f;
            /* Need temp buffer for f32 values since fp8 precision is too low */
            float* tmp = (float*)alloca(n * sizeof(float));
            for (size_t i = 0; i < n; i++) {
                tmp[i] = expf(fp8_e4m3_to_f32(px[i]) - max_val);
                sum += tmp[i];
            }
            for (size_t i = 0; i < n; i++) {
                d[i] = f32_to_fp8_e4m3(tmp[i] / sum);
            }
            break;
        }
        case DTYPE_F8_E5M2: {
            fp8_t* d = (fp8_t*)byte_array_ptr(dst);
            const fp8_t* px = (const fp8_t*)byte_array_ptr(x);
            float max_val = fp8_e5m2_to_f32(px[0]);
            for (size_t i = 1; i < n; i++) {
                float v = fp8_e5m2_to_f32(px[i]);
                if (v > max_val) max_val = v;
            }
            float sum = 0.0f;
            float* tmp = (float*)alloca(n * sizeof(float));
            for (size_t i = 0; i < n; i++) {
                tmp[i] = expf(fp8_e5m2_to_f32(px[i]) - max_val);
                sum += tmp[i];
            }
            for (size_t i = 0; i < n; i++) {
                d[i] = f32_to_fp8_e5m2(tmp[i] / sum);
            }
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
        case DTYPE_BF16: {
            bf16_t* py = (bf16_t*)byte_array_ptr(y);
            const bf16_t* px = (const bf16_t*)byte_array_ptr(x);
            float a = (float)alpha, b = (float)beta;
            for (size_t i = 0; i < n; i++) {
                py[i] = f32_to_bf16(a * bf16_to_f32(px[i]) + b * bf16_to_f32(py[i]));
            }
            break;
        }
        case DTYPE_F8_E4M3: {
            fp8_t* py = (fp8_t*)byte_array_ptr(y);
            const fp8_t* px = (const fp8_t*)byte_array_ptr(x);
            float a = (float)alpha, b = (float)beta;
            for (size_t i = 0; i < n; i++) {
                py[i] = f32_to_fp8_e4m3(a * fp8_e4m3_to_f32(px[i]) + b * fp8_e4m3_to_f32(py[i]));
            }
            break;
        }
        case DTYPE_F8_E5M2: {
            fp8_t* py = (fp8_t*)byte_array_ptr(y);
            const fp8_t* px = (const fp8_t*)byte_array_ptr(x);
            float a = (float)alpha, b = (float)beta;
            for (size_t i = 0; i < n; i++) {
                py[i] = f32_to_fp8_e5m2(a * fp8_e5m2_to_f32(px[i]) + b * fp8_e5m2_to_f32(py[i]));
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
        case DTYPE_BF16: {
            bf16_t* d = (bf16_t*)byte_array_ptr(dst);
            const bf16_t* s = (const bf16_t*)byte_array_ptr(src);
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
        case DTYPE_F8_E4M3:
        case DTYPE_F8_E5M2: {
            /* Both fp8 variants are 1 byte each */
            fp8_t* d = (fp8_t*)byte_array_ptr(dst);
            const fp8_t* s = (const fp8_t*)byte_array_ptr(src);
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
        case DTYPE_BF16: {
            bf16_t* d = (bf16_t*)byte_array_ptr(dst);
            for (size_t i = 0; i < n; i++) {
                d[i] = f32_to_bf16((float)u64_to_uniform(xoshiro256ss_next()));
            }
            break;
        }
        case DTYPE_F8_E4M3: {
            fp8_t* d = (fp8_t*)byte_array_ptr(dst);
            for (size_t i = 0; i < n; i++) {
                d[i] = f32_to_fp8_e4m3((float)u64_to_uniform(xoshiro256ss_next()));
            }
            break;
        }
        case DTYPE_F8_E5M2: {
            fp8_t* d = (fp8_t*)byte_array_ptr(dst);
            for (size_t i = 0; i < n; i++) {
                d[i] = f32_to_fp8_e5m2((float)u64_to_uniform(xoshiro256ss_next()));
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
        case DTYPE_BF16: {
            bf16_t* d = (bf16_t*)byte_array_ptr(dst);
            size_t i = 0;
            while (i + 1 < n) {
                double n1, n2;
                box_muller(&n1, &n2);
                d[i] = f32_to_bf16((float)n1);
                d[i + 1] = f32_to_bf16((float)n2);
                i += 2;
            }
            if (i < n) {
                double n1, tmp;
                box_muller(&n1, &tmp);
                d[i] = f32_to_bf16((float)n1);
            }
            break;
        }
        case DTYPE_F8_E4M3: {
            fp8_t* d = (fp8_t*)byte_array_ptr(dst);
            size_t i = 0;
            while (i + 1 < n) {
                double n1, n2;
                box_muller(&n1, &n2);
                d[i] = f32_to_fp8_e4m3((float)n1);
                d[i + 1] = f32_to_fp8_e4m3((float)n2);
                i += 2;
            }
            if (i < n) {
                double n1, tmp;
                box_muller(&n1, &tmp);
                d[i] = f32_to_fp8_e4m3((float)n1);
            }
            break;
        }
        case DTYPE_F8_E5M2: {
            fp8_t* d = (fp8_t*)byte_array_ptr(dst);
            size_t i = 0;
            while (i + 1 < n) {
                double n1, n2;
                box_muller(&n1, &n2);
                d[i] = f32_to_fp8_e5m2((float)n1);
                d[i + 1] = f32_to_fp8_e5m2((float)n2);
                i += 2;
            }
            if (i < n) {
                double n1, tmp;
                box_muller(&n1, &tmp);
                d[i] = f32_to_fp8_e5m2((float)n1);
            }
            break;
        }
        default: break;
    }
    return dst;
}
