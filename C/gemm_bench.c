/* Benchmark for generated GEMM kernels */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>

#include "gemm_gen.h"

/* Simple timing */
static double get_time_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000.0 + ts.tv_nsec / 1000000.0;
}

/* Fill array with random values */
static void fill_random(float* arr, size_t n) {
    for (size_t i = 0; i < n; i++) {
        arr[i] = (float)rand() / RAND_MAX;
    }
}

/* Compute reference result */
static void gemm_reference(float* C, const float* A, const float* B,
                           size_t M, size_t K, size_t N) {
    for (size_t i = 0; i < M; i++) {
        for (size_t j = 0; j < N; j++) {
            float sum = 0.0f;
            for (size_t k = 0; k < K; k++) {
                sum += A[i * K + k] * B[k * N + j];
            }
            C[i * N + j] = sum;
        }
    }
}

/* Check correctness with relative tolerance */
static int check_result(const float* C, const float* Cref, size_t n, float rel_tol) {
    for (size_t i = 0; i < n; i++) {
        float diff = C[i] - Cref[i];
        if (diff < 0) diff = -diff;
        float absref = Cref[i];
        if (absref < 0) absref = -absref;
        float tol = rel_tol * (absref > 1.0f ? absref : 1.0f);
        if (diff > tol) {
            printf("Mismatch at %zu: got %f, expected %f (diff=%e, tol=%e)\n",
                   i, C[i], Cref[i], diff, tol);
            return 0;
        }
    }
    return 1;
}

typedef void (*gemm_fn)(float*, const float*, const float*, size_t, size_t, size_t, float, float);

static void benchmark_kernel(const char* name, gemm_fn fn,
                             float* C, const float* A, const float* B,
                             size_t M, size_t K, size_t N, int warmup, int iters) {
    /* Warmup */
    for (int i = 0; i < warmup; i++) {
        memset(C, 0, M * N * sizeof(float));
        fn(C, A, B, M, K, N, 1.0f, 0.0f);
    }

    /* Timed runs */
    double total_ms = 0;
    for (int i = 0; i < iters; i++) {
        memset(C, 0, M * N * sizeof(float));
        double start = get_time_ms();
        fn(C, A, B, M, K, N, 1.0f, 0.0f);
        double end = get_time_ms();
        total_ms += (end - start);
    }

    double avg_ms = total_ms / iters;
    double flops = 2.0 * M * K * N;
    double gflops = flops / (avg_ms * 1e6);

    printf("  %-30s: %8.2f ms, %6.2f GFLOP/s\n", name, avg_ms, gflops);
}

int main(int argc, char** argv) {
    srand(42);

    size_t sizes[][3] = {
        {128, 128, 128},
        {256, 256, 256},
        {512, 512, 512},
        {1024, 1024, 1024}
    };
    int num_sizes = sizeof(sizes) / sizeof(sizes[0]);

    printf("=== Generated GEMM Kernel Benchmark ===\n\n");

    for (int s = 0; s < num_sizes; s++) {
        size_t M = sizes[s][0];
        size_t K = sizes[s][1];
        size_t N = sizes[s][2];

        printf("GEMM %zux%zu @ %zux%zu:\n", M, K, K, N);

        /* Allocate */
        float* A = (float*)malloc(M * K * sizeof(float));
        float* B = (float*)malloc(K * N * sizeof(float));
        float* C = (float*)malloc(M * N * sizeof(float));
        float* Cref = (float*)malloc(M * N * sizeof(float));

        fill_random(A, M * K);
        fill_random(B, K * N);

        /* Compute reference */
        gemm_reference(Cref, A, B, M, K, N);

        int warmup = 2;
        int iters = 5;

        /* Test each generated kernel */
        benchmark_kernel("4x4_k1 (baseline)", gemm_f32_gen_4x4_k1_t64, C, A, B, M, K, N, warmup, iters);
        if (!check_result(C, Cref, M*N, 1e-4f)) printf("    FAILED!\n");

        benchmark_kernel("8x8_k2 (tile=128)", gemm_f32_gen_8x8_k2_t128, C, A, B, M, K, N, warmup, iters);
        if (!check_result(C, Cref, M*N, 1e-4f)) printf("    FAILED!\n");

        benchmark_kernel("8x8_k4 (tile=128)", gemm_f32_gen_8x8_k4_t128, C, A, B, M, K, N, warmup, iters);
        if (!check_result(C, Cref, M*N, 1e-4f)) printf("    FAILED!\n");

        benchmark_kernel("8x8_k8 (tile=128)", gemm_f32_gen_8x8_k8_t128, C, A, B, M, K, N, warmup, iters);
        if (!check_result(C, Cref, M*N, 1e-4f)) printf("    FAILED!\n");

        benchmark_kernel("8x8_k4 (tile=64,K=256)", gemm_f32_gen_8x8_k4_t64, C, A, B, M, K, N, warmup, iters);
        if (!check_result(C, Cref, M*N, 1e-4f)) printf("    FAILED!\n");

        benchmark_kernel("8x8_k4 (tile=256,K=64)", gemm_f32_gen_8x8_k4_t256, C, A, B, M, K, N, warmup, iters);
        if (!check_result(C, Cref, M*N, 1e-4f)) printf("    FAILED!\n");

        printf("\n");

        free(A);
        free(B);
        free(C);
        free(Cref);
    }

    printf("Benchmark complete!\n");
    return 0;
}
