/* Benchmark OpenBLAS GEMM for comparison */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <cblas.h>
#include <mach/mach_time.h>

static double ns_per_tick = 0;

static void init_timer(void) {
    mach_timebase_info_data_t info;
    mach_timebase_info(&info);
    ns_per_tick = (double)info.numer / info.denom;
}

static uint64_t get_time_ns(void) {
    return (uint64_t)(mach_absolute_time() * ns_per_tick);
}

static void fill_random(float* arr, size_t n) {
    for (size_t i = 0; i < n; i++) {
        arr[i] = (float)rand() / RAND_MAX;
    }
}

/* Volatile sink to prevent optimization */
static volatile float sink = 0.0f;
static void use_result(const float* C, size_t n) {
    sink = C[n/2];
}

int main(int argc, char** argv) {
    init_timer();
    srand(42);

    size_t sizes[] = {128, 256, 512, 1024, 2048};
    int num_sizes = sizeof(sizes) / sizeof(sizes[0]);

    printf("=== OpenBLAS SGEMM Benchmark ===\n\n");

    for (int s = 0; s < num_sizes; s++) {
        size_t N = sizes[s];

        float* A = (float*)malloc(N * N * sizeof(float));
        float* B = (float*)malloc(N * N * sizeof(float));
        float* C = (float*)malloc(N * N * sizeof(float));

        fill_random(A, N * N);
        fill_random(B, N * N);

        int warmup = 3;
        int iters = N < 512 ? 20 : 5;

        /* Warmup */
        for (int i = 0; i < warmup; i++) {
            cblas_sgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans,
                        N, N, N, 1.0f, A, N, B, N, 0.0f, C, N);
            use_result(C, N*N);
        }

        /* Timed runs */
        uint64_t total_ns = 0;
        for (int i = 0; i < iters; i++) {
            uint64_t start = get_time_ns();
            cblas_sgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans,
                        N, N, N, 1.0f, A, N, B, N, 0.0f, C, N);
            use_result(C, N*N);
            uint64_t end = get_time_ns();
            total_ns += (end - start);
        }

        double avg_us = (double)total_ns / iters / 1000.0;
        double flops = 2.0 * N * N * N;
        double gflops = flops / avg_us / 1000.0;

        printf("GEMM %4zux%-4zu: %10.2f us, %7.2f GFLOP/s\n", N, N, avg_us, gflops);

        free(A);
        free(B);
        free(C);
    }

    return 0;
}
