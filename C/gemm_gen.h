/* Auto-generated GEMM kernels - DO NOT EDIT */
#pragma once

#include <arm_neon.h>
#include <stddef.h>


/* Generated NEON micro-kernel: 4x4, K-unroll=1 */
__attribute__((always_inline))
static inline void gemm_microkernel_4x4_k1_t64_neon(
    float* __restrict__ C, size_t ldc,
    const float* __restrict__ A, size_t lda,
    const float* __restrict__ B, size_t ldb,
    size_t K)
{
    float32x4_t c0_0 = vdupq_n_f32(0.0f);
    float32x4_t c1_0 = vdupq_n_f32(0.0f);
    float32x4_t c2_0 = vdupq_n_f32(0.0f);
    float32x4_t c3_0 = vdupq_n_f32(0.0f);
    size_t kk = 0;
    for (; kk < K; kk++) {
        float32x4_t a_col = {A[0*lda + (kk)], A[1*lda + (kk)], A[2*lda + (kk)], A[3*lda + (kk)]};
        float32x4_t b0_ = vld1q_f32(&B[(kk) * ldb + 0]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_, a_col, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_, a_col, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_, a_col, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_, a_col, 3);
    }
    vst1q_f32(&C[0*ldc + 0], vaddq_f32(vld1q_f32(&C[0*ldc + 0]), c0_0));
    vst1q_f32(&C[1*ldc + 0], vaddq_f32(vld1q_f32(&C[1*ldc + 0]), c1_0));
    vst1q_f32(&C[2*ldc + 0], vaddq_f32(vld1q_f32(&C[2*ldc + 0]), c2_0));
    vst1q_f32(&C[3*ldc + 0], vaddq_f32(vld1q_f32(&C[3*ldc + 0]), c3_0));
}


/* Generated tiled GEMM: MR=4, NR=4, tiles=64x64x64 */
__attribute__((always_inline))
static inline void gemm_f32_gen_4x4_k1_t64(
    float* __restrict__ C,
    const float* __restrict__ A,
    const float* __restrict__ B,
    size_t M, size_t K, size_t N,
    float alpha, float beta)
{
    if (beta != 1.0f) {
        for (size_t i = 0; i < M * N; i++) {
            C[i] *= beta;
        }
    }

    for (size_t i0 = 0; i0 < M; i0 += 64) {
        size_t i_end = (i0 + 64 < M) ? i0 + 64 : M;

        for (size_t j0 = 0; j0 < N; j0 += 64) {
            size_t j_end = (j0 + 64 < N) ? j0 + 64 : N;

            for (size_t k0 = 0; k0 < K; k0 += 64) {
                size_t k_end = (k0 + 64 < K) ? k0 + 64 : K;
                size_t tile_k = k_end - k0;

                size_t i;
                for (i = i0; i + 4 <= i_end; i += 4) {
                    size_t j;
                    for (j = j0; j + 4 <= j_end; j += 4) {
                        gemm_microkernel_4x4_k1_t64_neon(
                            &C[i * N + j], N,
                            &A[i * K + k0], K,
                            &B[k0 * N + j], N,
                            tile_k);
                    }
                    for (; j < j_end; j++) {
                        for (size_t ii = i; ii < i + 4; ii++) {
                            float sum = 0.0f;
                            for (size_t kk = k0; kk < k_end; kk++) {
                                sum += A[ii * K + kk] * B[kk * N + j];
                            }
                            C[ii * N + j] += sum;
                        }
                    }
                }
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

    if (alpha != 1.0f) {
        for (size_t i = 0; i < M * N; i++) {
            C[i] *= alpha;
        }
    }
}


/* Generated NEON micro-kernel: 8x8, K-unroll=2 */
__attribute__((always_inline))
static inline void gemm_microkernel_8x8_k2_t128_neon(
    float* __restrict__ C, size_t ldc,
    const float* __restrict__ A, size_t lda,
    const float* __restrict__ B, size_t ldb,
    size_t K)
{
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
    for (; kk + 2 <= K; kk += 2) {
        float32x4_t a0_u0 = {A[0*lda + (kk + 0)], A[1*lda + (kk + 0)], A[2*lda + (kk + 0)], A[3*lda + (kk + 0)]};
        float32x4_t a1_u0 = {A[4*lda + (kk + 0)], A[5*lda + (kk + 0)], A[6*lda + (kk + 0)], A[7*lda + (kk + 0)]};
        float32x4_t b0_u0 = vld1q_f32(&B[(kk + 0) * ldb + 0]);
        float32x4_t b1_u0 = vld1q_f32(&B[(kk + 0) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u0, a0_u0, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u0, a0_u0, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u0, a0_u0, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u0, a0_u0, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u0, a1_u0, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u0, a1_u0, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u0, a1_u0, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u0, a1_u0, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u0, a0_u0, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u0, a0_u0, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u0, a0_u0, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u0, a0_u0, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u0, a1_u0, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u0, a1_u0, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u0, a1_u0, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u0, a1_u0, 3);
        float32x4_t a0_u1 = {A[0*lda + (kk + 1)], A[1*lda + (kk + 1)], A[2*lda + (kk + 1)], A[3*lda + (kk + 1)]};
        float32x4_t a1_u1 = {A[4*lda + (kk + 1)], A[5*lda + (kk + 1)], A[6*lda + (kk + 1)], A[7*lda + (kk + 1)]};
        float32x4_t b0_u1 = vld1q_f32(&B[(kk + 1) * ldb + 0]);
        float32x4_t b1_u1 = vld1q_f32(&B[(kk + 1) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u1, a0_u1, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u1, a0_u1, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u1, a0_u1, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u1, a0_u1, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u1, a1_u1, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u1, a1_u1, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u1, a1_u1, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u1, a1_u1, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u1, a0_u1, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u1, a0_u1, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u1, a0_u1, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u1, a0_u1, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u1, a1_u1, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u1, a1_u1, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u1, a1_u1, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u1, a1_u1, 3);
    }
    for (; kk < K; kk++) {
        float32x4_t a0_r = {A[0*lda + (kk)], A[1*lda + (kk)], A[2*lda + (kk)], A[3*lda + (kk)]};
        float32x4_t a1_r = {A[4*lda + (kk)], A[5*lda + (kk)], A[6*lda + (kk)], A[7*lda + (kk)]};
        float32x4_t b0_r = vld1q_f32(&B[(kk) * ldb + 0]);
        float32x4_t b1_r = vld1q_f32(&B[(kk) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_r, a0_r, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_r, a0_r, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_r, a0_r, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_r, a0_r, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_r, a1_r, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_r, a1_r, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_r, a1_r, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_r, a1_r, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_r, a0_r, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_r, a0_r, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_r, a0_r, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_r, a0_r, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_r, a1_r, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_r, a1_r, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_r, a1_r, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_r, a1_r, 3);
    }
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


/* Generated tiled GEMM: MR=8, NR=8, tiles=128x128x128 */
__attribute__((always_inline))
static inline void gemm_f32_gen_8x8_k2_t128(
    float* __restrict__ C,
    const float* __restrict__ A,
    const float* __restrict__ B,
    size_t M, size_t K, size_t N,
    float alpha, float beta)
{
    if (beta != 1.0f) {
        for (size_t i = 0; i < M * N; i++) {
            C[i] *= beta;
        }
    }

    for (size_t i0 = 0; i0 < M; i0 += 128) {
        size_t i_end = (i0 + 128 < M) ? i0 + 128 : M;

        for (size_t j0 = 0; j0 < N; j0 += 128) {
            size_t j_end = (j0 + 128 < N) ? j0 + 128 : N;

            for (size_t k0 = 0; k0 < K; k0 += 128) {
                size_t k_end = (k0 + 128 < K) ? k0 + 128 : K;
                size_t tile_k = k_end - k0;

                size_t i;
                for (i = i0; i + 8 <= i_end; i += 8) {
                    size_t j;
                    for (j = j0; j + 8 <= j_end; j += 8) {
                        gemm_microkernel_8x8_k2_t128_neon(
                            &C[i * N + j], N,
                            &A[i * K + k0], K,
                            &B[k0 * N + j], N,
                            tile_k);
                    }
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

    if (alpha != 1.0f) {
        for (size_t i = 0; i < M * N; i++) {
            C[i] *= alpha;
        }
    }
}


/* Generated NEON micro-kernel: 8x8, K-unroll=4 */
__attribute__((always_inline))
static inline void gemm_microkernel_8x8_k4_t128_neon(
    float* __restrict__ C, size_t ldc,
    const float* __restrict__ A, size_t lda,
    const float* __restrict__ B, size_t ldb,
    size_t K)
{
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
    for (; kk + 4 <= K; kk += 4) {
        float32x4_t a0_u0 = {A[0*lda + (kk + 0)], A[1*lda + (kk + 0)], A[2*lda + (kk + 0)], A[3*lda + (kk + 0)]};
        float32x4_t a1_u0 = {A[4*lda + (kk + 0)], A[5*lda + (kk + 0)], A[6*lda + (kk + 0)], A[7*lda + (kk + 0)]};
        float32x4_t b0_u0 = vld1q_f32(&B[(kk + 0) * ldb + 0]);
        float32x4_t b1_u0 = vld1q_f32(&B[(kk + 0) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u0, a0_u0, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u0, a0_u0, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u0, a0_u0, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u0, a0_u0, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u0, a1_u0, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u0, a1_u0, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u0, a1_u0, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u0, a1_u0, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u0, a0_u0, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u0, a0_u0, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u0, a0_u0, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u0, a0_u0, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u0, a1_u0, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u0, a1_u0, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u0, a1_u0, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u0, a1_u0, 3);
        float32x4_t a0_u1 = {A[0*lda + (kk + 1)], A[1*lda + (kk + 1)], A[2*lda + (kk + 1)], A[3*lda + (kk + 1)]};
        float32x4_t a1_u1 = {A[4*lda + (kk + 1)], A[5*lda + (kk + 1)], A[6*lda + (kk + 1)], A[7*lda + (kk + 1)]};
        float32x4_t b0_u1 = vld1q_f32(&B[(kk + 1) * ldb + 0]);
        float32x4_t b1_u1 = vld1q_f32(&B[(kk + 1) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u1, a0_u1, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u1, a0_u1, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u1, a0_u1, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u1, a0_u1, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u1, a1_u1, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u1, a1_u1, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u1, a1_u1, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u1, a1_u1, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u1, a0_u1, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u1, a0_u1, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u1, a0_u1, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u1, a0_u1, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u1, a1_u1, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u1, a1_u1, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u1, a1_u1, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u1, a1_u1, 3);
        float32x4_t a0_u2 = {A[0*lda + (kk + 2)], A[1*lda + (kk + 2)], A[2*lda + (kk + 2)], A[3*lda + (kk + 2)]};
        float32x4_t a1_u2 = {A[4*lda + (kk + 2)], A[5*lda + (kk + 2)], A[6*lda + (kk + 2)], A[7*lda + (kk + 2)]};
        float32x4_t b0_u2 = vld1q_f32(&B[(kk + 2) * ldb + 0]);
        float32x4_t b1_u2 = vld1q_f32(&B[(kk + 2) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u2, a0_u2, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u2, a0_u2, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u2, a0_u2, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u2, a0_u2, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u2, a1_u2, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u2, a1_u2, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u2, a1_u2, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u2, a1_u2, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u2, a0_u2, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u2, a0_u2, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u2, a0_u2, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u2, a0_u2, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u2, a1_u2, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u2, a1_u2, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u2, a1_u2, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u2, a1_u2, 3);
        float32x4_t a0_u3 = {A[0*lda + (kk + 3)], A[1*lda + (kk + 3)], A[2*lda + (kk + 3)], A[3*lda + (kk + 3)]};
        float32x4_t a1_u3 = {A[4*lda + (kk + 3)], A[5*lda + (kk + 3)], A[6*lda + (kk + 3)], A[7*lda + (kk + 3)]};
        float32x4_t b0_u3 = vld1q_f32(&B[(kk + 3) * ldb + 0]);
        float32x4_t b1_u3 = vld1q_f32(&B[(kk + 3) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u3, a0_u3, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u3, a0_u3, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u3, a0_u3, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u3, a0_u3, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u3, a1_u3, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u3, a1_u3, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u3, a1_u3, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u3, a1_u3, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u3, a0_u3, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u3, a0_u3, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u3, a0_u3, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u3, a0_u3, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u3, a1_u3, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u3, a1_u3, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u3, a1_u3, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u3, a1_u3, 3);
    }
    for (; kk < K; kk++) {
        float32x4_t a0_r = {A[0*lda + (kk)], A[1*lda + (kk)], A[2*lda + (kk)], A[3*lda + (kk)]};
        float32x4_t a1_r = {A[4*lda + (kk)], A[5*lda + (kk)], A[6*lda + (kk)], A[7*lda + (kk)]};
        float32x4_t b0_r = vld1q_f32(&B[(kk) * ldb + 0]);
        float32x4_t b1_r = vld1q_f32(&B[(kk) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_r, a0_r, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_r, a0_r, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_r, a0_r, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_r, a0_r, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_r, a1_r, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_r, a1_r, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_r, a1_r, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_r, a1_r, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_r, a0_r, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_r, a0_r, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_r, a0_r, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_r, a0_r, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_r, a1_r, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_r, a1_r, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_r, a1_r, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_r, a1_r, 3);
    }
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


/* Generated tiled GEMM: MR=8, NR=8, tiles=128x128x128 */
__attribute__((always_inline))
static inline void gemm_f32_gen_8x8_k4_t128(
    float* __restrict__ C,
    const float* __restrict__ A,
    const float* __restrict__ B,
    size_t M, size_t K, size_t N,
    float alpha, float beta)
{
    if (beta != 1.0f) {
        for (size_t i = 0; i < M * N; i++) {
            C[i] *= beta;
        }
    }

    for (size_t i0 = 0; i0 < M; i0 += 128) {
        size_t i_end = (i0 + 128 < M) ? i0 + 128 : M;

        for (size_t j0 = 0; j0 < N; j0 += 128) {
            size_t j_end = (j0 + 128 < N) ? j0 + 128 : N;

            for (size_t k0 = 0; k0 < K; k0 += 128) {
                size_t k_end = (k0 + 128 < K) ? k0 + 128 : K;
                size_t tile_k = k_end - k0;

                size_t i;
                for (i = i0; i + 8 <= i_end; i += 8) {
                    size_t j;
                    for (j = j0; j + 8 <= j_end; j += 8) {
                        gemm_microkernel_8x8_k4_t128_neon(
                            &C[i * N + j], N,
                            &A[i * K + k0], K,
                            &B[k0 * N + j], N,
                            tile_k);
                    }
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

    if (alpha != 1.0f) {
        for (size_t i = 0; i < M * N; i++) {
            C[i] *= alpha;
        }
    }
}


/* Generated NEON micro-kernel: 8x8, K-unroll=8 */
__attribute__((always_inline))
static inline void gemm_microkernel_8x8_k8_t128_neon(
    float* __restrict__ C, size_t ldc,
    const float* __restrict__ A, size_t lda,
    const float* __restrict__ B, size_t ldb,
    size_t K)
{
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
    for (; kk + 8 <= K; kk += 8) {
        float32x4_t a0_u0 = {A[0*lda + (kk + 0)], A[1*lda + (kk + 0)], A[2*lda + (kk + 0)], A[3*lda + (kk + 0)]};
        float32x4_t a1_u0 = {A[4*lda + (kk + 0)], A[5*lda + (kk + 0)], A[6*lda + (kk + 0)], A[7*lda + (kk + 0)]};
        float32x4_t b0_u0 = vld1q_f32(&B[(kk + 0) * ldb + 0]);
        float32x4_t b1_u0 = vld1q_f32(&B[(kk + 0) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u0, a0_u0, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u0, a0_u0, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u0, a0_u0, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u0, a0_u0, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u0, a1_u0, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u0, a1_u0, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u0, a1_u0, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u0, a1_u0, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u0, a0_u0, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u0, a0_u0, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u0, a0_u0, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u0, a0_u0, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u0, a1_u0, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u0, a1_u0, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u0, a1_u0, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u0, a1_u0, 3);
        float32x4_t a0_u1 = {A[0*lda + (kk + 1)], A[1*lda + (kk + 1)], A[2*lda + (kk + 1)], A[3*lda + (kk + 1)]};
        float32x4_t a1_u1 = {A[4*lda + (kk + 1)], A[5*lda + (kk + 1)], A[6*lda + (kk + 1)], A[7*lda + (kk + 1)]};
        float32x4_t b0_u1 = vld1q_f32(&B[(kk + 1) * ldb + 0]);
        float32x4_t b1_u1 = vld1q_f32(&B[(kk + 1) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u1, a0_u1, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u1, a0_u1, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u1, a0_u1, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u1, a0_u1, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u1, a1_u1, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u1, a1_u1, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u1, a1_u1, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u1, a1_u1, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u1, a0_u1, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u1, a0_u1, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u1, a0_u1, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u1, a0_u1, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u1, a1_u1, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u1, a1_u1, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u1, a1_u1, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u1, a1_u1, 3);
        float32x4_t a0_u2 = {A[0*lda + (kk + 2)], A[1*lda + (kk + 2)], A[2*lda + (kk + 2)], A[3*lda + (kk + 2)]};
        float32x4_t a1_u2 = {A[4*lda + (kk + 2)], A[5*lda + (kk + 2)], A[6*lda + (kk + 2)], A[7*lda + (kk + 2)]};
        float32x4_t b0_u2 = vld1q_f32(&B[(kk + 2) * ldb + 0]);
        float32x4_t b1_u2 = vld1q_f32(&B[(kk + 2) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u2, a0_u2, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u2, a0_u2, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u2, a0_u2, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u2, a0_u2, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u2, a1_u2, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u2, a1_u2, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u2, a1_u2, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u2, a1_u2, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u2, a0_u2, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u2, a0_u2, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u2, a0_u2, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u2, a0_u2, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u2, a1_u2, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u2, a1_u2, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u2, a1_u2, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u2, a1_u2, 3);
        float32x4_t a0_u3 = {A[0*lda + (kk + 3)], A[1*lda + (kk + 3)], A[2*lda + (kk + 3)], A[3*lda + (kk + 3)]};
        float32x4_t a1_u3 = {A[4*lda + (kk + 3)], A[5*lda + (kk + 3)], A[6*lda + (kk + 3)], A[7*lda + (kk + 3)]};
        float32x4_t b0_u3 = vld1q_f32(&B[(kk + 3) * ldb + 0]);
        float32x4_t b1_u3 = vld1q_f32(&B[(kk + 3) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u3, a0_u3, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u3, a0_u3, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u3, a0_u3, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u3, a0_u3, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u3, a1_u3, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u3, a1_u3, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u3, a1_u3, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u3, a1_u3, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u3, a0_u3, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u3, a0_u3, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u3, a0_u3, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u3, a0_u3, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u3, a1_u3, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u3, a1_u3, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u3, a1_u3, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u3, a1_u3, 3);
        float32x4_t a0_u4 = {A[0*lda + (kk + 4)], A[1*lda + (kk + 4)], A[2*lda + (kk + 4)], A[3*lda + (kk + 4)]};
        float32x4_t a1_u4 = {A[4*lda + (kk + 4)], A[5*lda + (kk + 4)], A[6*lda + (kk + 4)], A[7*lda + (kk + 4)]};
        float32x4_t b0_u4 = vld1q_f32(&B[(kk + 4) * ldb + 0]);
        float32x4_t b1_u4 = vld1q_f32(&B[(kk + 4) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u4, a0_u4, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u4, a0_u4, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u4, a0_u4, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u4, a0_u4, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u4, a1_u4, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u4, a1_u4, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u4, a1_u4, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u4, a1_u4, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u4, a0_u4, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u4, a0_u4, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u4, a0_u4, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u4, a0_u4, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u4, a1_u4, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u4, a1_u4, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u4, a1_u4, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u4, a1_u4, 3);
        float32x4_t a0_u5 = {A[0*lda + (kk + 5)], A[1*lda + (kk + 5)], A[2*lda + (kk + 5)], A[3*lda + (kk + 5)]};
        float32x4_t a1_u5 = {A[4*lda + (kk + 5)], A[5*lda + (kk + 5)], A[6*lda + (kk + 5)], A[7*lda + (kk + 5)]};
        float32x4_t b0_u5 = vld1q_f32(&B[(kk + 5) * ldb + 0]);
        float32x4_t b1_u5 = vld1q_f32(&B[(kk + 5) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u5, a0_u5, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u5, a0_u5, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u5, a0_u5, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u5, a0_u5, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u5, a1_u5, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u5, a1_u5, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u5, a1_u5, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u5, a1_u5, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u5, a0_u5, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u5, a0_u5, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u5, a0_u5, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u5, a0_u5, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u5, a1_u5, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u5, a1_u5, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u5, a1_u5, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u5, a1_u5, 3);
        float32x4_t a0_u6 = {A[0*lda + (kk + 6)], A[1*lda + (kk + 6)], A[2*lda + (kk + 6)], A[3*lda + (kk + 6)]};
        float32x4_t a1_u6 = {A[4*lda + (kk + 6)], A[5*lda + (kk + 6)], A[6*lda + (kk + 6)], A[7*lda + (kk + 6)]};
        float32x4_t b0_u6 = vld1q_f32(&B[(kk + 6) * ldb + 0]);
        float32x4_t b1_u6 = vld1q_f32(&B[(kk + 6) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u6, a0_u6, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u6, a0_u6, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u6, a0_u6, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u6, a0_u6, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u6, a1_u6, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u6, a1_u6, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u6, a1_u6, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u6, a1_u6, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u6, a0_u6, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u6, a0_u6, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u6, a0_u6, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u6, a0_u6, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u6, a1_u6, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u6, a1_u6, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u6, a1_u6, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u6, a1_u6, 3);
        float32x4_t a0_u7 = {A[0*lda + (kk + 7)], A[1*lda + (kk + 7)], A[2*lda + (kk + 7)], A[3*lda + (kk + 7)]};
        float32x4_t a1_u7 = {A[4*lda + (kk + 7)], A[5*lda + (kk + 7)], A[6*lda + (kk + 7)], A[7*lda + (kk + 7)]};
        float32x4_t b0_u7 = vld1q_f32(&B[(kk + 7) * ldb + 0]);
        float32x4_t b1_u7 = vld1q_f32(&B[(kk + 7) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u7, a0_u7, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u7, a0_u7, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u7, a0_u7, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u7, a0_u7, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u7, a1_u7, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u7, a1_u7, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u7, a1_u7, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u7, a1_u7, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u7, a0_u7, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u7, a0_u7, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u7, a0_u7, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u7, a0_u7, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u7, a1_u7, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u7, a1_u7, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u7, a1_u7, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u7, a1_u7, 3);
    }
    for (; kk < K; kk++) {
        float32x4_t a0_r = {A[0*lda + (kk)], A[1*lda + (kk)], A[2*lda + (kk)], A[3*lda + (kk)]};
        float32x4_t a1_r = {A[4*lda + (kk)], A[5*lda + (kk)], A[6*lda + (kk)], A[7*lda + (kk)]};
        float32x4_t b0_r = vld1q_f32(&B[(kk) * ldb + 0]);
        float32x4_t b1_r = vld1q_f32(&B[(kk) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_r, a0_r, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_r, a0_r, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_r, a0_r, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_r, a0_r, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_r, a1_r, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_r, a1_r, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_r, a1_r, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_r, a1_r, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_r, a0_r, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_r, a0_r, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_r, a0_r, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_r, a0_r, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_r, a1_r, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_r, a1_r, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_r, a1_r, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_r, a1_r, 3);
    }
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


/* Generated tiled GEMM: MR=8, NR=8, tiles=128x128x128 */
__attribute__((always_inline))
static inline void gemm_f32_gen_8x8_k8_t128(
    float* __restrict__ C,
    const float* __restrict__ A,
    const float* __restrict__ B,
    size_t M, size_t K, size_t N,
    float alpha, float beta)
{
    if (beta != 1.0f) {
        for (size_t i = 0; i < M * N; i++) {
            C[i] *= beta;
        }
    }

    for (size_t i0 = 0; i0 < M; i0 += 128) {
        size_t i_end = (i0 + 128 < M) ? i0 + 128 : M;

        for (size_t j0 = 0; j0 < N; j0 += 128) {
            size_t j_end = (j0 + 128 < N) ? j0 + 128 : N;

            for (size_t k0 = 0; k0 < K; k0 += 128) {
                size_t k_end = (k0 + 128 < K) ? k0 + 128 : K;
                size_t tile_k = k_end - k0;

                size_t i;
                for (i = i0; i + 8 <= i_end; i += 8) {
                    size_t j;
                    for (j = j0; j + 8 <= j_end; j += 8) {
                        gemm_microkernel_8x8_k8_t128_neon(
                            &C[i * N + j], N,
                            &A[i * K + k0], K,
                            &B[k0 * N + j], N,
                            tile_k);
                    }
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

    if (alpha != 1.0f) {
        for (size_t i = 0; i < M * N; i++) {
            C[i] *= alpha;
        }
    }
}


/* Generated NEON micro-kernel: 8x8, K-unroll=4 */
__attribute__((always_inline))
static inline void gemm_microkernel_8x8_k4_t64_neon(
    float* __restrict__ C, size_t ldc,
    const float* __restrict__ A, size_t lda,
    const float* __restrict__ B, size_t ldb,
    size_t K)
{
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
    for (; kk + 4 <= K; kk += 4) {
        float32x4_t a0_u0 = {A[0*lda + (kk + 0)], A[1*lda + (kk + 0)], A[2*lda + (kk + 0)], A[3*lda + (kk + 0)]};
        float32x4_t a1_u0 = {A[4*lda + (kk + 0)], A[5*lda + (kk + 0)], A[6*lda + (kk + 0)], A[7*lda + (kk + 0)]};
        float32x4_t b0_u0 = vld1q_f32(&B[(kk + 0) * ldb + 0]);
        float32x4_t b1_u0 = vld1q_f32(&B[(kk + 0) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u0, a0_u0, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u0, a0_u0, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u0, a0_u0, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u0, a0_u0, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u0, a1_u0, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u0, a1_u0, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u0, a1_u0, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u0, a1_u0, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u0, a0_u0, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u0, a0_u0, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u0, a0_u0, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u0, a0_u0, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u0, a1_u0, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u0, a1_u0, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u0, a1_u0, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u0, a1_u0, 3);
        float32x4_t a0_u1 = {A[0*lda + (kk + 1)], A[1*lda + (kk + 1)], A[2*lda + (kk + 1)], A[3*lda + (kk + 1)]};
        float32x4_t a1_u1 = {A[4*lda + (kk + 1)], A[5*lda + (kk + 1)], A[6*lda + (kk + 1)], A[7*lda + (kk + 1)]};
        float32x4_t b0_u1 = vld1q_f32(&B[(kk + 1) * ldb + 0]);
        float32x4_t b1_u1 = vld1q_f32(&B[(kk + 1) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u1, a0_u1, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u1, a0_u1, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u1, a0_u1, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u1, a0_u1, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u1, a1_u1, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u1, a1_u1, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u1, a1_u1, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u1, a1_u1, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u1, a0_u1, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u1, a0_u1, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u1, a0_u1, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u1, a0_u1, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u1, a1_u1, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u1, a1_u1, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u1, a1_u1, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u1, a1_u1, 3);
        float32x4_t a0_u2 = {A[0*lda + (kk + 2)], A[1*lda + (kk + 2)], A[2*lda + (kk + 2)], A[3*lda + (kk + 2)]};
        float32x4_t a1_u2 = {A[4*lda + (kk + 2)], A[5*lda + (kk + 2)], A[6*lda + (kk + 2)], A[7*lda + (kk + 2)]};
        float32x4_t b0_u2 = vld1q_f32(&B[(kk + 2) * ldb + 0]);
        float32x4_t b1_u2 = vld1q_f32(&B[(kk + 2) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u2, a0_u2, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u2, a0_u2, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u2, a0_u2, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u2, a0_u2, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u2, a1_u2, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u2, a1_u2, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u2, a1_u2, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u2, a1_u2, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u2, a0_u2, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u2, a0_u2, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u2, a0_u2, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u2, a0_u2, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u2, a1_u2, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u2, a1_u2, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u2, a1_u2, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u2, a1_u2, 3);
        float32x4_t a0_u3 = {A[0*lda + (kk + 3)], A[1*lda + (kk + 3)], A[2*lda + (kk + 3)], A[3*lda + (kk + 3)]};
        float32x4_t a1_u3 = {A[4*lda + (kk + 3)], A[5*lda + (kk + 3)], A[6*lda + (kk + 3)], A[7*lda + (kk + 3)]};
        float32x4_t b0_u3 = vld1q_f32(&B[(kk + 3) * ldb + 0]);
        float32x4_t b1_u3 = vld1q_f32(&B[(kk + 3) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u3, a0_u3, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u3, a0_u3, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u3, a0_u3, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u3, a0_u3, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u3, a1_u3, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u3, a1_u3, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u3, a1_u3, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u3, a1_u3, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u3, a0_u3, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u3, a0_u3, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u3, a0_u3, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u3, a0_u3, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u3, a1_u3, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u3, a1_u3, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u3, a1_u3, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u3, a1_u3, 3);
    }
    for (; kk < K; kk++) {
        float32x4_t a0_r = {A[0*lda + (kk)], A[1*lda + (kk)], A[2*lda + (kk)], A[3*lda + (kk)]};
        float32x4_t a1_r = {A[4*lda + (kk)], A[5*lda + (kk)], A[6*lda + (kk)], A[7*lda + (kk)]};
        float32x4_t b0_r = vld1q_f32(&B[(kk) * ldb + 0]);
        float32x4_t b1_r = vld1q_f32(&B[(kk) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_r, a0_r, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_r, a0_r, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_r, a0_r, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_r, a0_r, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_r, a1_r, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_r, a1_r, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_r, a1_r, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_r, a1_r, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_r, a0_r, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_r, a0_r, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_r, a0_r, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_r, a0_r, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_r, a1_r, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_r, a1_r, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_r, a1_r, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_r, a1_r, 3);
    }
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


/* Generated tiled GEMM: MR=8, NR=8, tiles=64x64x256 */
__attribute__((always_inline))
static inline void gemm_f32_gen_8x8_k4_t64(
    float* __restrict__ C,
    const float* __restrict__ A,
    const float* __restrict__ B,
    size_t M, size_t K, size_t N,
    float alpha, float beta)
{
    if (beta != 1.0f) {
        for (size_t i = 0; i < M * N; i++) {
            C[i] *= beta;
        }
    }

    for (size_t i0 = 0; i0 < M; i0 += 64) {
        size_t i_end = (i0 + 64 < M) ? i0 + 64 : M;

        for (size_t j0 = 0; j0 < N; j0 += 64) {
            size_t j_end = (j0 + 64 < N) ? j0 + 64 : N;

            for (size_t k0 = 0; k0 < K; k0 += 256) {
                size_t k_end = (k0 + 256 < K) ? k0 + 256 : K;
                size_t tile_k = k_end - k0;

                size_t i;
                for (i = i0; i + 8 <= i_end; i += 8) {
                    size_t j;
                    for (j = j0; j + 8 <= j_end; j += 8) {
                        gemm_microkernel_8x8_k4_t64_neon(
                            &C[i * N + j], N,
                            &A[i * K + k0], K,
                            &B[k0 * N + j], N,
                            tile_k);
                    }
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

    if (alpha != 1.0f) {
        for (size_t i = 0; i < M * N; i++) {
            C[i] *= alpha;
        }
    }
}


/* Generated NEON micro-kernel: 8x8, K-unroll=4 */
__attribute__((always_inline))
static inline void gemm_microkernel_8x8_k4_t256_neon(
    float* __restrict__ C, size_t ldc,
    const float* __restrict__ A, size_t lda,
    const float* __restrict__ B, size_t ldb,
    size_t K)
{
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
    for (; kk + 4 <= K; kk += 4) {
        float32x4_t a0_u0 = {A[0*lda + (kk + 0)], A[1*lda + (kk + 0)], A[2*lda + (kk + 0)], A[3*lda + (kk + 0)]};
        float32x4_t a1_u0 = {A[4*lda + (kk + 0)], A[5*lda + (kk + 0)], A[6*lda + (kk + 0)], A[7*lda + (kk + 0)]};
        float32x4_t b0_u0 = vld1q_f32(&B[(kk + 0) * ldb + 0]);
        float32x4_t b1_u0 = vld1q_f32(&B[(kk + 0) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u0, a0_u0, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u0, a0_u0, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u0, a0_u0, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u0, a0_u0, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u0, a1_u0, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u0, a1_u0, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u0, a1_u0, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u0, a1_u0, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u0, a0_u0, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u0, a0_u0, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u0, a0_u0, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u0, a0_u0, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u0, a1_u0, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u0, a1_u0, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u0, a1_u0, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u0, a1_u0, 3);
        float32x4_t a0_u1 = {A[0*lda + (kk + 1)], A[1*lda + (kk + 1)], A[2*lda + (kk + 1)], A[3*lda + (kk + 1)]};
        float32x4_t a1_u1 = {A[4*lda + (kk + 1)], A[5*lda + (kk + 1)], A[6*lda + (kk + 1)], A[7*lda + (kk + 1)]};
        float32x4_t b0_u1 = vld1q_f32(&B[(kk + 1) * ldb + 0]);
        float32x4_t b1_u1 = vld1q_f32(&B[(kk + 1) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u1, a0_u1, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u1, a0_u1, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u1, a0_u1, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u1, a0_u1, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u1, a1_u1, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u1, a1_u1, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u1, a1_u1, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u1, a1_u1, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u1, a0_u1, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u1, a0_u1, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u1, a0_u1, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u1, a0_u1, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u1, a1_u1, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u1, a1_u1, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u1, a1_u1, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u1, a1_u1, 3);
        float32x4_t a0_u2 = {A[0*lda + (kk + 2)], A[1*lda + (kk + 2)], A[2*lda + (kk + 2)], A[3*lda + (kk + 2)]};
        float32x4_t a1_u2 = {A[4*lda + (kk + 2)], A[5*lda + (kk + 2)], A[6*lda + (kk + 2)], A[7*lda + (kk + 2)]};
        float32x4_t b0_u2 = vld1q_f32(&B[(kk + 2) * ldb + 0]);
        float32x4_t b1_u2 = vld1q_f32(&B[(kk + 2) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u2, a0_u2, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u2, a0_u2, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u2, a0_u2, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u2, a0_u2, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u2, a1_u2, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u2, a1_u2, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u2, a1_u2, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u2, a1_u2, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u2, a0_u2, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u2, a0_u2, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u2, a0_u2, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u2, a0_u2, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u2, a1_u2, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u2, a1_u2, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u2, a1_u2, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u2, a1_u2, 3);
        float32x4_t a0_u3 = {A[0*lda + (kk + 3)], A[1*lda + (kk + 3)], A[2*lda + (kk + 3)], A[3*lda + (kk + 3)]};
        float32x4_t a1_u3 = {A[4*lda + (kk + 3)], A[5*lda + (kk + 3)], A[6*lda + (kk + 3)], A[7*lda + (kk + 3)]};
        float32x4_t b0_u3 = vld1q_f32(&B[(kk + 3) * ldb + 0]);
        float32x4_t b1_u3 = vld1q_f32(&B[(kk + 3) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_u3, a0_u3, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_u3, a0_u3, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_u3, a0_u3, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_u3, a0_u3, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_u3, a1_u3, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_u3, a1_u3, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_u3, a1_u3, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_u3, a1_u3, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_u3, a0_u3, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_u3, a0_u3, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_u3, a0_u3, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_u3, a0_u3, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_u3, a1_u3, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_u3, a1_u3, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_u3, a1_u3, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_u3, a1_u3, 3);
    }
    for (; kk < K; kk++) {
        float32x4_t a0_r = {A[0*lda + (kk)], A[1*lda + (kk)], A[2*lda + (kk)], A[3*lda + (kk)]};
        float32x4_t a1_r = {A[4*lda + (kk)], A[5*lda + (kk)], A[6*lda + (kk)], A[7*lda + (kk)]};
        float32x4_t b0_r = vld1q_f32(&B[(kk) * ldb + 0]);
        float32x4_t b1_r = vld1q_f32(&B[(kk) * ldb + 4]);
        c0_0 = vmlaq_laneq_f32(c0_0, b0_r, a0_r, 0);
        c1_0 = vmlaq_laneq_f32(c1_0, b0_r, a0_r, 1);
        c2_0 = vmlaq_laneq_f32(c2_0, b0_r, a0_r, 2);
        c3_0 = vmlaq_laneq_f32(c3_0, b0_r, a0_r, 3);
        c4_0 = vmlaq_laneq_f32(c4_0, b0_r, a1_r, 0);
        c5_0 = vmlaq_laneq_f32(c5_0, b0_r, a1_r, 1);
        c6_0 = vmlaq_laneq_f32(c6_0, b0_r, a1_r, 2);
        c7_0 = vmlaq_laneq_f32(c7_0, b0_r, a1_r, 3);
        c0_1 = vmlaq_laneq_f32(c0_1, b1_r, a0_r, 0);
        c1_1 = vmlaq_laneq_f32(c1_1, b1_r, a0_r, 1);
        c2_1 = vmlaq_laneq_f32(c2_1, b1_r, a0_r, 2);
        c3_1 = vmlaq_laneq_f32(c3_1, b1_r, a0_r, 3);
        c4_1 = vmlaq_laneq_f32(c4_1, b1_r, a1_r, 0);
        c5_1 = vmlaq_laneq_f32(c5_1, b1_r, a1_r, 1);
        c6_1 = vmlaq_laneq_f32(c6_1, b1_r, a1_r, 2);
        c7_1 = vmlaq_laneq_f32(c7_1, b1_r, a1_r, 3);
    }
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


/* Generated tiled GEMM: MR=8, NR=8, tiles=256x256x64 */
__attribute__((always_inline))
static inline void gemm_f32_gen_8x8_k4_t256(
    float* __restrict__ C,
    const float* __restrict__ A,
    const float* __restrict__ B,
    size_t M, size_t K, size_t N,
    float alpha, float beta)
{
    if (beta != 1.0f) {
        for (size_t i = 0; i < M * N; i++) {
            C[i] *= beta;
        }
    }

    for (size_t i0 = 0; i0 < M; i0 += 256) {
        size_t i_end = (i0 + 256 < M) ? i0 + 256 : M;

        for (size_t j0 = 0; j0 < N; j0 += 256) {
            size_t j_end = (j0 + 256 < N) ? j0 + 256 : N;

            for (size_t k0 = 0; k0 < K; k0 += 64) {
                size_t k_end = (k0 + 64 < K) ? k0 + 64 : K;
                size_t tile_k = k_end - k0;

                size_t i;
                for (i = i0; i + 8 <= i_end; i += 8) {
                    size_t j;
                    for (j = j0; j + 8 <= j_end; j += 8) {
                        gemm_microkernel_8x8_k4_t256_neon(
                            &C[i * N + j], N,
                            &A[i * K + k0], K,
                            &B[k0 * N + j], N,
                            tile_k);
                    }
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

    if (alpha != 1.0f) {
        for (size_t i = 0; i < M * N; i++) {
            C[i] *= alpha;
        }
    }
}


