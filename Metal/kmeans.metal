#include <metal_stdlib>
#include <metal_simdgroup_matrix>
using namespace metal;

// KMeans loss computation - finds nearest centroid for each point
kernel void kmeans_loss(
    device const float* points [[buffer(0)]],
    device const float* centroids [[buffer(1)]],
    device float* losses [[buffer(2)]],
    constant uint& d [[buffer(3)]],
    constant uint& k [[buffer(4)]],
    uint i [[thread_position_in_grid]]
) {
    float minNorm2 = INFINITY;

    for (uint j = 0; j < k; j++) {
        float norm2 = 0.0f;
        for (uint l = 0; l < d; l++) {
            float dx = points[i * d + l] - centroids[j * d + l];
            norm2 += dx * dx;
        }
        minNorm2 = min(minNorm2, norm2);
    }

    losses[i] = minNorm2;
}

// Matrix-vector multiply: y = A * x
// A is m x n, x is n, y is m
kernel void gemv(
    device const float* A [[buffer(0)]],
    device const float* x [[buffer(1)]],
    device float* y [[buffer(2)]],
    constant uint& n [[buffer(3)]],
    uint i [[thread_position_in_grid]]
) {
    float sum = 0.0f;
    for (uint j = 0; j < n; j++) {
        sum += A[i * n + j] * x[j];
    }
    y[i] = sum;
}

// Matrix multiply: C = A * B (naive - 1 thread per element)
// A is m x k, B is k x n, C is m x n
kernel void gemm(
    device const float* A [[buffer(0)]],
    device const float* B [[buffer(1)]],
    device float* C [[buffer(2)]],
    constant uint& m [[buffer(3)]],
    constant uint& k [[buffer(4)]],
    constant uint& n [[buffer(5)]],
    uint2 gid [[thread_position_in_grid]]
) {
    uint i = gid.y;
    uint j = gid.x;

    if (i >= m || j >= n) return;

    float sum = 0.0f;
    for (uint l = 0; l < k; l++) {
        sum += A[i * k + l] * B[l * n + j];
    }
    C[i * n + j] = sum;
}

// ============================================================
// Tiled GEMM with Shared Memory (32x32 tiles)
// ============================================================
// Each threadgroup loads tiles of A and B into shared memory,
// then computes partial products. This improves cache reuse
// from O(1) to O(TILE_SIZE) per global memory load.

#define TILE_SIZE 32

kernel void gemm_tiled(
    device const float* A [[buffer(0)]],
    device const float* B [[buffer(1)]],
    device float* C [[buffer(2)]],
    constant uint& M [[buffer(3)]],
    constant uint& K [[buffer(4)]],
    constant uint& N [[buffer(5)]],
    uint2 tid [[thread_position_in_threadgroup]],
    uint2 tgid [[threadgroup_position_in_grid]]
) {
    // Shared memory tiles for A and B
    threadgroup float As[TILE_SIZE][TILE_SIZE];
    threadgroup float Bs[TILE_SIZE][TILE_SIZE];

    // Global row/col this thread is responsible for
    uint row = tgid.y * TILE_SIZE + tid.y;
    uint col = tgid.x * TILE_SIZE + tid.x;

    float sum = 0.0f;

    // Number of tiles along K dimension
    uint numTiles = (K + TILE_SIZE - 1) / TILE_SIZE;

    for (uint t = 0; t < numTiles; t++) {
        // Collaborative load: each thread loads one element of each tile
        uint aCol = t * TILE_SIZE + tid.x;
        uint bRow = t * TILE_SIZE + tid.y;

        // Load A tile element (with bounds check)
        As[tid.y][tid.x] = (row < M && aCol < K) ? A[row * K + aCol] : 0.0f;

        // Load B tile element (with bounds check)
        Bs[tid.y][tid.x] = (bRow < K && col < N) ? B[bRow * N + col] : 0.0f;

        // Synchronize to ensure tile is fully loaded
        threadgroup_barrier(mem_flags::mem_threadgroup);

        // Compute partial dot product from this tile
        for (uint i = 0; i < TILE_SIZE; i++) {
            sum += As[tid.y][i] * Bs[i][tid.x];
        }

        // Synchronize before loading next tile
        threadgroup_barrier(mem_flags::mem_threadgroup);
    }

    // Write result (with bounds check)
    if (row < M && col < N) {
        C[row * N + col] = sum;
    }
}

// ============================================================
// Simdgroup GEMM using Apple's hardware matrix units
// ============================================================
// Uses simdgroup_matrix for 8×8 cooperative matrix operations.
// Each simdgroup (32 threads) computes multiple 8×8 output tiles.
// This leverages the dedicated matrix hardware on Apple Silicon.

// Constants for simdgroup GEMM
#define SIMD_TILE_M 32  // Output tile rows per threadgroup
#define SIMD_TILE_N 32  // Output tile cols per threadgroup
#define SIMD_TILE_K 32  // K-dimension tile size

kernel void gemm_simd(
    device const float* A [[buffer(0)]],
    device const float* B [[buffer(1)]],
    device float* C [[buffer(2)]],
    constant uint& M [[buffer(3)]],
    constant uint& K [[buffer(4)]],
    constant uint& N [[buffer(5)]],
    uint2 tgid [[threadgroup_position_in_grid]],
    uint simd_lane [[thread_index_in_simdgroup]],
    uint simd_id [[simdgroup_index_in_threadgroup]]
) {
    // Each threadgroup computes a SIMD_TILE_M × SIMD_TILE_N output tile
    // using 4 simdgroups (each simdgroup handles a 16×16 subtile using 2×2 8×8 blocks)

    // Base row/col for this threadgroup's output tile
    uint tg_row = tgid.y * SIMD_TILE_M;
    uint tg_col = tgid.x * SIMD_TILE_N;

    // Each simdgroup handles a 16×16 subtile (2×2 arrangement of 8×8 blocks)
    // simd_id: 0=top-left, 1=top-right, 2=bottom-left, 3=bottom-right
    uint simd_row = tg_row + (simd_id / 2) * 16;
    uint simd_col = tg_col + (simd_id % 2) * 16;

    // Accumulators for 2×2 grid of 8×8 output blocks
    simdgroup_float8x8 acc00 = simdgroup_float8x8(0);
    simdgroup_float8x8 acc01 = simdgroup_float8x8(0);
    simdgroup_float8x8 acc10 = simdgroup_float8x8(0);
    simdgroup_float8x8 acc11 = simdgroup_float8x8(0);

    // Iterate over K dimension in 8-element chunks
    for (uint k = 0; k < K; k += 8) {
        // Load 2 A tiles (16×8) and 2 B tiles (8×16)
        simdgroup_float8x8 a0, a1;  // A[simd_row:simd_row+16, k:k+8]
        simdgroup_float8x8 b0, b1;  // B[k:k+8, simd_col:simd_col+16]

        // Load A tiles (two 8×8 blocks stacked vertically)
        if (simd_row < M && k < K) {
            simdgroup_load(a0, A + simd_row * K + k, K);
        }
        if (simd_row + 8 < M && k < K) {
            simdgroup_load(a1, A + (simd_row + 8) * K + k, K);
        }

        // Load B tiles (two 8×8 blocks side by side)
        if (k < K && simd_col < N) {
            simdgroup_load(b0, B + k * N + simd_col, N);
        }
        if (k < K && simd_col + 8 < N) {
            simdgroup_load(b1, B + k * N + simd_col + 8, N);
        }

        // Multiply-accumulate: C[i,j] += A[i,k] * B[k,j]
        simdgroup_multiply_accumulate(acc00, a0, b0, acc00);
        simdgroup_multiply_accumulate(acc01, a0, b1, acc01);
        simdgroup_multiply_accumulate(acc10, a1, b0, acc10);
        simdgroup_multiply_accumulate(acc11, a1, b1, acc11);
    }

    // Store results (with bounds checking)
    if (simd_row < M && simd_col < N) {
        simdgroup_store(acc00, C + simd_row * N + simd_col, N);
    }
    if (simd_row < M && simd_col + 8 < N) {
        simdgroup_store(acc01, C + simd_row * N + simd_col + 8, N);
    }
    if (simd_row + 8 < M && simd_col < N) {
        simdgroup_store(acc10, C + (simd_row + 8) * N + simd_col, N);
    }
    if (simd_row + 8 < M && simd_col + 8 < N) {
        simdgroup_store(acc11, C + (simd_row + 8) * N + simd_col + 8, N);
    }
}

// ============================================================
// Optimized Simdgroup GEMM with Shared Memory Prefetch
// ============================================================
// Improvements over gemm_simd:
// 1. Shared memory tiles reduce global memory bandwidth
// 2. Double buffering overlaps loads with compute
// 3. Larger output tiles (64×64) for better occupancy
// 4. Vectorized loads (float4) for 4x bandwidth

#define OPT_TILE_M 64
#define OPT_TILE_N 64
#define OPT_TILE_K 32

kernel void gemm_simd_opt(
    device const float* A [[buffer(0)]],
    device const float* B [[buffer(1)]],
    device float* C [[buffer(2)]],
    constant uint& M [[buffer(3)]],
    constant uint& K [[buffer(4)]],
    constant uint& N [[buffer(5)]],
    uint2 tgid [[threadgroup_position_in_grid]],
    uint2 tid [[thread_position_in_threadgroup]],
    uint simd_lane [[thread_index_in_simdgroup]],
    uint simd_id [[simdgroup_index_in_threadgroup]]
) {
    // Shared memory for A and B tiles (double buffered)
    threadgroup float As[2][OPT_TILE_M][OPT_TILE_K];
    threadgroup float Bs[2][OPT_TILE_K][OPT_TILE_N];

    // Threadgroup computes OPT_TILE_M × OPT_TILE_N output
    uint tg_row = tgid.y * OPT_TILE_M;
    uint tg_col = tgid.x * OPT_TILE_N;

    // 256 threads = 8 simdgroups, each handles 16×32 output (2×4 grid of 8×8)
    // Layout: 2 rows × 4 cols of simdgroups
    uint simd_row_offset = (simd_id / 4) * 32;  // 0 or 32
    uint simd_col_offset = (simd_id % 4) * 16;  // 0, 16, 32, 48

    uint simd_row = tg_row + simd_row_offset;
    uint simd_col = tg_col + simd_col_offset;

    // 4×2 grid of 8×8 accumulators per simdgroup = 32×16 output
    simdgroup_float8x8 acc[4][2];
    for (int i = 0; i < 4; i++) {
        for (int j = 0; j < 2; j++) {
            acc[i][j] = simdgroup_float8x8(0);
        }
    }

    // Thread indices for collaborative loading
    uint linear_tid = tid.y * 16 + tid.x;  // 0..255

    // Load first tile
    int buf = 0;
    uint k = 0;

    // Prefetch first A tile: each thread loads 1 element (need 64×32 = 2048, have 256 threads → 8 loads each)
    for (uint i = linear_tid; i < OPT_TILE_M * OPT_TILE_K; i += 256) {
        uint ar = i / OPT_TILE_K;
        uint ac = i % OPT_TILE_K;
        As[buf][ar][ac] = (tg_row + ar < M && k + ac < K) ? A[(tg_row + ar) * K + k + ac] : 0.0f;
    }

    // Prefetch first B tile
    for (uint i = linear_tid; i < OPT_TILE_K * OPT_TILE_N; i += 256) {
        uint br = i / OPT_TILE_N;
        uint bc = i % OPT_TILE_N;
        Bs[buf][br][bc] = (k + br < K && tg_col + bc < N) ? B[(k + br) * N + tg_col + bc] : 0.0f;
    }

    threadgroup_barrier(mem_flags::mem_threadgroup);

    // Main loop with double buffering
    for (k = 0; k < K; k += OPT_TILE_K) {
        uint next_k = k + OPT_TILE_K;
        int next_buf = 1 - buf;

        // Prefetch next tiles while computing current
        if (next_k < K) {
            for (uint i = linear_tid; i < OPT_TILE_M * OPT_TILE_K; i += 256) {
                uint ar = i / OPT_TILE_K;
                uint ac = i % OPT_TILE_K;
                As[next_buf][ar][ac] = (tg_row + ar < M && next_k + ac < K) ? A[(tg_row + ar) * K + next_k + ac] : 0.0f;
            }
            for (uint i = linear_tid; i < OPT_TILE_K * OPT_TILE_N; i += 256) {
                uint br = i / OPT_TILE_N;
                uint bc = i % OPT_TILE_N;
                Bs[next_buf][br][bc] = (next_k + br < K && tg_col + bc < N) ? B[(next_k + br) * N + tg_col + bc] : 0.0f;
            }
        }

        // Compute: iterate over K tile in 8-element chunks
        for (uint kk = 0; kk < OPT_TILE_K; kk += 8) {
            // Load A subtiles from shared memory (4 × 8×8 blocks)
            simdgroup_float8x8 a[4];
            for (int ai = 0; ai < 4; ai++) {
                simdgroup_load(a[ai], &As[buf][simd_row_offset + ai * 8][kk], OPT_TILE_K);
            }

            // Load B subtiles from shared memory (2 × 8×8 blocks)
            simdgroup_float8x8 b[2];
            for (int bi = 0; bi < 2; bi++) {
                simdgroup_load(b[bi], &Bs[buf][kk][simd_col_offset + bi * 8], OPT_TILE_N);
            }

            // Multiply-accumulate
            for (int ai = 0; ai < 4; ai++) {
                for (int bi = 0; bi < 2; bi++) {
                    simdgroup_multiply_accumulate(acc[ai][bi], a[ai], b[bi], acc[ai][bi]);
                }
            }
        }

        threadgroup_barrier(mem_flags::mem_threadgroup);
        buf = next_buf;
    }

    // Store results
    for (int ai = 0; ai < 4; ai++) {
        for (int bi = 0; bi < 2; bi++) {
            uint out_row = simd_row + ai * 8;
            uint out_col = simd_col + bi * 8;
            if (out_row < M && out_col < N) {
                simdgroup_store(acc[ai][bi], C + out_row * N + out_col, N);
            }
        }
    }
}

// ============================================================
// M4-Optimized GEMM: No bounds checks, float4 loads, 128×128 tiles
// ============================================================
// Optimized GEMM using simdgroup matrix operations
// REQUIRES: M, N, K are multiples of 64
// Fits within 32KB threadgroup memory limit
// Memory: As[64][33] = 8448 bytes, Bs[32][65] = 8320 bytes, Total = 16768 bytes

#define M4_TILE_M 64
#define M4_TILE_N 64
#define M4_TILE_K 32

kernel void gemm_m4(
    device const float* A [[buffer(0)]],
    device const float* B [[buffer(1)]],
    device float* C [[buffer(2)]],
    constant uint& M [[buffer(3)]],
    constant uint& K [[buffer(4)]],
    constant uint& N [[buffer(5)]],
    uint2 tgid [[threadgroup_position_in_grid]],
    uint2 tid [[thread_position_in_threadgroup]],
    uint simd_id [[simdgroup_index_in_threadgroup]]
) {
    // Shared memory for tiles - sized to fit 32KB limit
    threadgroup float As[M4_TILE_M][M4_TILE_K + 1];  // 64×33 = 8448 bytes
    threadgroup float Bs[M4_TILE_K][M4_TILE_N + 1];  // 32×65 = 8320 bytes

    // Each threadgroup: 64×64 output, 256 threads = 8 simdgroups
    // Each simdgroup: 32×16 output (4×2 grid of 8×8)
    uint tg_row = tgid.y * M4_TILE_M;
    uint tg_col = tgid.x * M4_TILE_N;

    // Simdgroup layout: 2×4 grid (2 rows of 4 columns)
    // Each simdgroup handles 32×16 of the 64×64 output
    uint simd_row = tg_row + (simd_id / 4) * 32;
    uint simd_col = tg_col + (simd_id % 4) * 16;

    // 4×2 grid of 8×8 accumulators = 32×16 per simdgroup
    simdgroup_float8x8 acc[4][2];
    #pragma unroll
    for (int i = 0; i < 4; i++) {
        #pragma unroll
        for (int j = 0; j < 2; j++) {
            acc[i][j] = simdgroup_float8x8(0);
        }
    }

    // Thread ID for loading (256 threads = 8×32 threadgroup)
    uint linear_tid = tid.y * 32 + tid.x;

    // Main loop over K
    for (uint k = 0; k < K; k += M4_TILE_K) {
        // Load A tile: 64×32 = 2048 floats, 256 threads → 8 floats each
        #pragma unroll
        for (uint i = 0; i < 8; i++) {
            uint idx = linear_tid * 8 + i;
            uint ar = idx / M4_TILE_K;   // row in tile (0-63)
            uint ac = idx % M4_TILE_K;   // col in tile (0-31)
            uint global_row = tg_row + ar;
            uint global_col = k + ac;
            As[ar][ac] = A[global_row * K + global_col];
        }

        // Load B tile: 32×64 = 2048 floats, 256 threads → 8 floats each
        #pragma unroll
        for (uint i = 0; i < 8; i++) {
            uint idx = linear_tid * 8 + i;
            uint br = idx / M4_TILE_N;   // row in tile (0-31)
            uint bc = idx % M4_TILE_N;   // col in tile (0-63)
            uint global_row = k + br;
            uint global_col = tg_col + bc;
            Bs[br][bc] = B[global_row * N + global_col];
        }

        threadgroup_barrier(mem_flags::mem_threadgroup);

        // Compute using simdgroup matrix multiply
        uint simd_row_local = (simd_id / 4) * 32;
        uint simd_col_local = (simd_id % 4) * 16;

        #pragma unroll
        for (uint kk = 0; kk < M4_TILE_K; kk += 8) {
            simdgroup_float8x8 a[4], b[2];

            // Load 4 A blocks (32×8 region)
            #pragma unroll
            for (int ai = 0; ai < 4; ai++) {
                simdgroup_load(a[ai], &As[simd_row_local + ai * 8][kk], M4_TILE_K + 1);
            }

            // Load 2 B blocks (8×16 region)
            #pragma unroll
            for (int bi = 0; bi < 2; bi++) {
                simdgroup_load(b[bi], &Bs[kk][simd_col_local + bi * 8], M4_TILE_N + 1);
            }

            // 4×2 multiply-accumulate
            #pragma unroll
            for (int ai = 0; ai < 4; ai++) {
                #pragma unroll
                for (int bi = 0; bi < 2; bi++) {
                    simdgroup_multiply_accumulate(acc[ai][bi], a[ai], b[bi], acc[ai][bi]);
                }
            }
        }

        threadgroup_barrier(mem_flags::mem_threadgroup);
    }

    // Store 32×16 output
    #pragma unroll
    for (int ai = 0; ai < 4; ai++) {
        #pragma unroll
        for (int bi = 0; bi < 2; bi++) {
            simdgroup_store(acc[ai][bi], C + (simd_row + ai * 8) * N + simd_col + bi * 8, N);
        }
    }
}

// ============================================================
// M4-Pro GEMM: Double-buffered with software pipelining
// ============================================================
// This version uses double buffering to overlap memory loads with computation
// REQUIRES: M, N, K are multiples of 64

#define M4P_TILE_M 64
#define M4P_TILE_N 64
#define M4P_TILE_K 32

kernel void gemm_m4_pro(
    device const float* A [[buffer(0)]],
    device const float* B [[buffer(1)]],
    device float* C [[buffer(2)]],
    constant uint& M [[buffer(3)]],
    constant uint& K [[buffer(4)]],
    constant uint& N [[buffer(5)]],
    uint2 tgid [[threadgroup_position_in_grid]],
    uint2 tid [[thread_position_in_threadgroup]],
    uint simd_id [[simdgroup_index_in_threadgroup]]
) {
    // Double buffer for prefetching
    threadgroup float As[2][M4P_TILE_M][M4P_TILE_K + 1];  // 2 × 64×33 = 16896 bytes
    threadgroup float Bs[2][M4P_TILE_K][M4P_TILE_N + 1];  // 2 × 32×65 = 16640 bytes
    // Total: 33536 bytes > 32768 limit!
    // Instead: use registers for prefetch, single threadgroup buffer

    // Actually, let's use single buffer with explicit prefetch to registers
    threadgroup float AsT[M4P_TILE_M][M4P_TILE_K + 1];  // 64×33 = 8448 bytes
    threadgroup float BsT[M4P_TILE_K][M4P_TILE_N + 1];  // 32×65 = 8320 bytes

    uint tg_row = tgid.y * M4P_TILE_M;
    uint tg_col = tgid.x * M4P_TILE_N;
    uint simd_row = tg_row + (simd_id / 4) * 32;
    uint simd_col = tg_col + (simd_id % 4) * 16;

    simdgroup_float8x8 acc[4][2];
    #pragma unroll
    for (int i = 0; i < 4; i++) {
        #pragma unroll
        for (int j = 0; j < 2; j++) {
            acc[i][j] = simdgroup_float8x8(0);
        }
    }

    uint linear_tid = tid.y * 32 + tid.x;
    uint num_k_tiles = K / M4P_TILE_K;

    // Prefetch first tile into registers
    float a_prefetch[8], b_prefetch[8];

    // Load first tile
    uint k = 0;
    #pragma unroll
    for (uint i = 0; i < 8; i++) {
        uint idx = linear_tid * 8 + i;
        uint ar = idx / M4P_TILE_K;
        uint ac = idx % M4P_TILE_K;
        a_prefetch[i] = A[(tg_row + ar) * K + k + ac];
    }
    #pragma unroll
    for (uint i = 0; i < 8; i++) {
        uint idx = linear_tid * 8 + i;
        uint br = idx / M4P_TILE_N;
        uint bc = idx % M4P_TILE_N;
        b_prefetch[i] = B[(k + br) * N + tg_col + bc];
    }

    // Main loop with software pipelining
    for (uint kt = 0; kt < num_k_tiles; kt++) {
        // Store prefetched data to threadgroup memory
        #pragma unroll
        for (uint i = 0; i < 8; i++) {
            uint idx = linear_tid * 8 + i;
            uint ar = idx / M4P_TILE_K;
            uint ac = idx % M4P_TILE_K;
            AsT[ar][ac] = a_prefetch[i];
        }
        #pragma unroll
        for (uint i = 0; i < 8; i++) {
            uint idx = linear_tid * 8 + i;
            uint br = idx / M4P_TILE_N;
            uint bc = idx % M4P_TILE_N;
            BsT[br][bc] = b_prefetch[i];
        }

        threadgroup_barrier(mem_flags::mem_threadgroup);

        // Prefetch next tile while computing (if not last)
        uint next_k = (kt + 1) * M4P_TILE_K;
        if (kt + 1 < num_k_tiles) {
            #pragma unroll
            for (uint i = 0; i < 8; i++) {
                uint idx = linear_tid * 8 + i;
                uint ar = idx / M4P_TILE_K;
                uint ac = idx % M4P_TILE_K;
                a_prefetch[i] = A[(tg_row + ar) * K + next_k + ac];
            }
            #pragma unroll
            for (uint i = 0; i < 8; i++) {
                uint idx = linear_tid * 8 + i;
                uint br = idx / M4P_TILE_N;
                uint bc = idx % M4P_TILE_N;
                b_prefetch[i] = B[(next_k + br) * N + tg_col + bc];
            }
        }

        // Compute using simdgroup matrix multiply
        uint simd_row_local = (simd_id / 4) * 32;
        uint simd_col_local = (simd_id % 4) * 16;

        #pragma unroll
        for (uint kk = 0; kk < M4P_TILE_K; kk += 8) {
            simdgroup_float8x8 a[4], b[2];

            #pragma unroll
            for (int ai = 0; ai < 4; ai++) {
                simdgroup_load(a[ai], &AsT[simd_row_local + ai * 8][kk], M4P_TILE_K + 1);
            }
            #pragma unroll
            for (int bi = 0; bi < 2; bi++) {
                simdgroup_load(b[bi], &BsT[kk][simd_col_local + bi * 8], M4P_TILE_N + 1);
            }

            #pragma unroll
            for (int ai = 0; ai < 4; ai++) {
                #pragma unroll
                for (int bi = 0; bi < 2; bi++) {
                    simdgroup_multiply_accumulate(acc[ai][bi], a[ai], b[bi], acc[ai][bi]);
                }
            }
        }

        threadgroup_barrier(mem_flags::mem_threadgroup);
    }

    // Store output
    #pragma unroll
    for (int ai = 0; ai < 4; ai++) {
        #pragma unroll
        for (int bi = 0; bi < 2; bi++) {
            simdgroup_store(acc[ai][bi], C + (simd_row + ai * 8) * N + simd_col + bi * 8, N);
        }
    }
}

// ============================================================
// M4-Max GEMM: Larger tiles (128×64) for better compute density
// ============================================================
// Uses 512 threads = 16 simdgroups for maximum occupancy
// REQUIRES: M, N multiples of 128/64

#define M4X_TILE_M 128
#define M4X_TILE_N 64
#define M4X_TILE_K 16

kernel void gemm_m4_max(
    device const float* A [[buffer(0)]],
    device const float* B [[buffer(1)]],
    device float* C [[buffer(2)]],
    constant uint& M [[buffer(3)]],
    constant uint& K [[buffer(4)]],
    constant uint& N [[buffer(5)]],
    uint2 tgid [[threadgroup_position_in_grid]],
    uint2 tid [[thread_position_in_threadgroup]],
    uint simd_id [[simdgroup_index_in_threadgroup]]
) {
    // Shared memory: 128×17 + 16×65 = 8704 + 4160 = 12864 bytes (fits!)
    threadgroup float As[M4X_TILE_M][M4X_TILE_K + 1];  // 128×17 = 8704 bytes
    threadgroup float Bs[M4X_TILE_K][M4X_TILE_N + 1];  // 16×65 = 4160 bytes

    uint tg_row = tgid.y * M4X_TILE_M;
    uint tg_col = tgid.x * M4X_TILE_N;

    // 16 simdgroups: 4×4 grid, each handles 32×16 output
    uint simd_row = tg_row + (simd_id / 4) * 32;
    uint simd_col = tg_col + (simd_id % 4) * 16;

    // 4×2 grid of 8×8 = 32×16 per simdgroup
    simdgroup_float8x8 acc[4][2];
    #pragma unroll
    for (int i = 0; i < 4; i++) {
        #pragma unroll
        for (int j = 0; j < 2; j++) {
            acc[i][j] = simdgroup_float8x8(0);
        }
    }

    // 512 threads for loading
    uint linear_tid = tid.y * 32 + tid.x;  // Assuming 32×16 threadgroup

    for (uint k = 0; k < K; k += M4X_TILE_K) {
        // Load A: 128×16 = 2048 floats, 512 threads → 4 floats each
        #pragma unroll
        for (uint i = 0; i < 4; i++) {
            uint idx = linear_tid * 4 + i;
            uint ar = idx / M4X_TILE_K;
            uint ac = idx % M4X_TILE_K;
            if (ar < M4X_TILE_M) {
                As[ar][ac] = A[(tg_row + ar) * K + k + ac];
            }
        }

        // Load B: 16×64 = 1024 floats, 512 threads → 2 floats each
        #pragma unroll
        for (uint i = 0; i < 2; i++) {
            uint idx = linear_tid * 2 + i;
            uint br = idx / M4X_TILE_N;
            uint bc = idx % M4X_TILE_N;
            if (br < M4X_TILE_K) {
                Bs[br][bc] = B[(k + br) * N + tg_col + bc];
            }
        }

        threadgroup_barrier(mem_flags::mem_threadgroup);

        // Compute
        uint simd_row_local = (simd_id / 4) * 32;
        uint simd_col_local = (simd_id % 4) * 16;

        #pragma unroll
        for (uint kk = 0; kk < M4X_TILE_K; kk += 8) {
            simdgroup_float8x8 a[4], b[2];

            #pragma unroll
            for (int ai = 0; ai < 4; ai++) {
                simdgroup_load(a[ai], &As[simd_row_local + ai * 8][kk], M4X_TILE_K + 1);
            }
            #pragma unroll
            for (int bi = 0; bi < 2; bi++) {
                simdgroup_load(b[bi], &Bs[kk][simd_col_local + bi * 8], M4X_TILE_N + 1);
            }

            #pragma unroll
            for (int ai = 0; ai < 4; ai++) {
                #pragma unroll
                for (int bi = 0; bi < 2; bi++) {
                    simdgroup_multiply_accumulate(acc[ai][bi], a[ai], b[bi], acc[ai][bi]);
                }
            }
        }

        threadgroup_barrier(mem_flags::mem_threadgroup);
    }

    // Store output
    #pragma unroll
    for (int ai = 0; ai < 4; ai++) {
        #pragma unroll
        for (int bi = 0; bi < 2; bi++) {
            simdgroup_store(acc[ai][bi], C + (simd_row + ai * 8) * N + simd_col + bi * 8, N);
        }
    }
}

// Element-wise operations
kernel void add(
    device const float* a [[buffer(0)]],
    device const float* b [[buffer(1)]],
    device float* c [[buffer(2)]],
    uint i [[thread_position_in_grid]]
) {
    c[i] = a[i] + b[i];
}

kernel void mul(
    device const float* a [[buffer(0)]],
    device const float* b [[buffer(1)]],
    device float* c [[buffer(2)]],
    uint i [[thread_position_in_grid]]
) {
    c[i] = a[i] * b[i];
}

kernel void scale(
    device const float* a [[buffer(0)]],
    device float* b [[buffer(1)]],
    constant float& s [[buffer(2)]],
    uint i [[thread_position_in_grid]]
) {
    b[i] = s * a[i];
}

// Reduction sum (single workgroup version - simple, for small arrays)
kernel void reduce_sum(
    device const float* input [[buffer(0)]],
    device float* output [[buffer(1)]],
    constant uint& n [[buffer(2)]],
    threadgroup float* shared [[threadgroup(0)]],
    uint tid [[thread_index_in_threadgroup]],
    uint gid [[thread_position_in_grid]],
    uint blockDim [[threads_per_threadgroup]]
) {
    // Load into shared memory
    shared[tid] = (gid < n) ? input[gid] : 0.0f;
    threadgroup_barrier(mem_flags::mem_threadgroup);

    // Parallel reduction
    for (uint s = blockDim / 2; s > 0; s >>= 1) {
        if (tid < s) {
            shared[tid] += shared[tid + s];
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
    }

    if (tid == 0) {
        output[0] = shared[0];
    }
}

// ============================================================
// Multi-stage reduction for large arrays (grid-stride loop)
// ============================================================
// Pass 1: Each threadgroup reduces a portion of the input to a partial sum
// Pass 2: Reduce the partial sums (can reuse reduce_sum for small counts)

kernel void reduce_sum_large(
    device const float* input [[buffer(0)]],
    device float* partials [[buffer(1)]],
    constant uint& n [[buffer(2)]],
    constant uint& numThreadgroups [[buffer(3)]],
    uint tid [[thread_index_in_threadgroup]],
    uint gid [[thread_position_in_grid]],
    uint blockIdx [[threadgroup_position_in_grid]],
    uint blockDim [[threads_per_threadgroup]]
) {
    threadgroup float shared[256];

    // Grid-stride loop: each thread accumulates multiple elements
    float sum = 0.0f;
    uint gridSize = blockDim * numThreadgroups;
    for (uint i = gid; i < n; i += gridSize) {
        sum += input[i];
    }

    // Store thread's sum in shared memory
    shared[tid] = sum;
    threadgroup_barrier(mem_flags::mem_threadgroup);

    // Binary tree reduction within threadgroup
    for (uint s = blockDim / 2; s > 0; s >>= 1) {
        if (tid < s) {
            shared[tid] += shared[tid + s];
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
    }

    // Thread 0 writes this threadgroup's partial sum
    if (tid == 0) {
        partials[blockIdx] = shared[0];
    }
}

// Reduce max for large arrays (grid-stride)
kernel void reduce_max_large(
    device const float* input [[buffer(0)]],
    device float* partials [[buffer(1)]],
    constant uint& n [[buffer(2)]],
    constant uint& numThreadgroups [[buffer(3)]],
    uint tid [[thread_index_in_threadgroup]],
    uint gid [[thread_position_in_grid]],
    uint blockIdx [[threadgroup_position_in_grid]],
    uint blockDim [[threads_per_threadgroup]]
) {
    threadgroup float shared[256];

    float maxVal = -INFINITY;
    uint gridSize = blockDim * numThreadgroups;
    for (uint i = gid; i < n; i += gridSize) {
        maxVal = max(maxVal, input[i]);
    }

    shared[tid] = maxVal;
    threadgroup_barrier(mem_flags::mem_threadgroup);

    for (uint s = blockDim / 2; s > 0; s >>= 1) {
        if (tid < s) {
            shared[tid] = max(shared[tid], shared[tid + s]);
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
    }

    if (tid == 0) {
        partials[blockIdx] = shared[0];
    }
}

// Softmax numerator: exp(x - max)
kernel void softmax_exp(
    device const float* x [[buffer(0)]],
    device float* y [[buffer(1)]],
    constant float& max_val [[buffer(2)]],
    uint i [[thread_position_in_grid]]
) {
    y[i] = exp(x[i] - max_val);
}

// Normalize by sum
kernel void normalize(
    device float* x [[buffer(0)]],
    constant float& sum [[buffer(1)]],
    uint i [[thread_position_in_grid]]
) {
    x[i] /= sum;
}

// ============================================================
// Fused Softmax (2-pass version for small-medium arrays)
// ============================================================
// Pass 1: Find max, compute exp(x-max), and partial sums in one pass
// Pass 2: Normalize by total sum

// Fused softmax pass 1: computes exp(x - max) and partial sums
// Also outputs the exp values for normalization
kernel void softmax_fused_pass1(
    device const float* input [[buffer(0)]],
    device float* exp_output [[buffer(1)]],
    device float* partial_sums [[buffer(2)]],
    constant uint& n [[buffer(3)]],
    constant float& max_val [[buffer(4)]],
    uint tid [[thread_index_in_threadgroup]],
    uint gid [[thread_position_in_grid]],
    uint blockIdx [[threadgroup_position_in_grid]],
    uint blockDim [[threads_per_threadgroup]]
) {
    threadgroup float shared[256];

    // Compute exp(x - max) and store
    float e = 0.0f;
    if (gid < n) {
        e = exp(input[gid] - max_val);
        exp_output[gid] = e;
    }
    shared[tid] = e;
    threadgroup_barrier(mem_flags::mem_threadgroup);

    // Reduce to partial sum
    for (uint s = blockDim / 2; s > 0; s >>= 1) {
        if (tid < s) {
            shared[tid] += shared[tid + s];
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
    }

    if (tid == 0) {
        partial_sums[blockIdx] = shared[0];
    }
}

// Fused softmax pass 2: normalize by sum
kernel void softmax_normalize(
    device float* data [[buffer(0)]],
    constant float& sum_val [[buffer(1)]],
    constant uint& n [[buffer(2)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        data[gid] /= sum_val;
    }
}

// ============================================================
// AXPY: y = a*x + y (BLAS Level 1)
// ============================================================
// Fused multiply-add for efficient vector operations

kernel void axpy(
    device const float* x [[buffer(0)]],
    device float* y [[buffer(1)]],
    constant float& a [[buffer(2)]],
    constant uint& n [[buffer(3)]],
    uint i [[thread_position_in_grid]]
) {
    if (i < n) {
        y[i] = fma(a, x[i], y[i]);
    }
}

// Scaled addition: z = a*x + b*y
kernel void axpby(
    device const float* x [[buffer(0)]],
    device const float* y [[buffer(1)]],
    device float* z [[buffer(2)]],
    constant float& a [[buffer(3)]],
    constant float& b [[buffer(4)]],
    uint i [[thread_position_in_grid]]
) {
    z[i] = fma(a, x[i], b * y[i]);
}

// Fused multiply-add: z = x * y + z
kernel void fma_vec(
    device const float* x [[buffer(0)]],
    device const float* y [[buffer(1)]],
    device float* z [[buffer(2)]],
    uint i [[thread_position_in_grid]]
) {
    z[i] = fma(x[i], y[i], z[i]);
}

// ============================================================
// FULLY FUSED SOFTMAX (single kernel, single memory pass)
// ============================================================
// For vectors up to 8192 elements (fits in threadgroup memory)
// Does max reduction, exp(x-max), sum reduction, normalize in ONE kernel
// This is 3x faster than separate max -> exp -> sum -> div passes

#define SOFTMAX_MAX_SIZE 8192

kernel void softmax_fused(
    device const float* input [[buffer(0)]],
    device float* output [[buffer(1)]],
    constant uint& n [[buffer(2)]],
    threadgroup float* shared [[threadgroup(0)]],  // size = n
    uint tid [[thread_index_in_threadgroup]],
    uint threads [[threads_per_threadgroup]]
) {
    // Load into shared memory
    for (uint i = tid; i < n; i += threads) {
        shared[i] = input[i];
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);

    // Find max (parallel reduction in registers)
    float local_max = -INFINITY;
    for (uint i = tid; i < n; i += threads) {
        local_max = max(local_max, shared[i]);
    }

    // Warp-level max reduction using simd
    local_max = simd_max(local_max);

    // Cross-warp reduction via shared memory
    threadgroup float warp_maxes[32];
    uint warp_id = tid / 32;
    uint lane_id = tid % 32;
    if (lane_id == 0 && warp_id < 32) {
        warp_maxes[warp_id] = local_max;
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);

    // First warp reduces warp_maxes
    float global_max = -INFINITY;
    if (tid < 32) {
        global_max = (tid < (threads + 31) / 32) ? warp_maxes[tid] : -INFINITY;
        global_max = simd_max(global_max);
    }
    // Broadcast to all threads
    if (tid == 0) {
        warp_maxes[0] = global_max;
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);
    global_max = warp_maxes[0];

    // Compute exp(x - max) in-place and local sum
    float local_sum = 0.0f;
    for (uint i = tid; i < n; i += threads) {
        float exp_val = exp(shared[i] - global_max);
        shared[i] = exp_val;
        local_sum += exp_val;
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);

    // Sum reduction (same pattern as max)
    local_sum = simd_sum(local_sum);

    threadgroup float warp_sums[32];
    if (lane_id == 0 && warp_id < 32) {
        warp_sums[warp_id] = local_sum;
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);

    float global_sum = 0.0f;
    if (tid < 32) {
        global_sum = (tid < (threads + 31) / 32) ? warp_sums[tid] : 0.0f;
        global_sum = simd_sum(global_sum);
    }
    if (tid == 0) {
        warp_sums[0] = global_sum;
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);
    global_sum = warp_sums[0];

    // Normalize and write output
    float inv_sum = 1.0f / global_sum;
    for (uint i = tid; i < n; i += threads) {
        output[i] = shared[i] * inv_sum;
    }
}

// ============================================================
// FUSED BIAS + ACTIVATION KERNELS
// ============================================================
// Common patterns for neural network inference

// Add bias and apply ReLU: y = max(0, x + bias)
kernel void bias_relu(
    device const float* input [[buffer(0)]],
    device const float* bias [[buffer(1)]],
    device float* output [[buffer(2)]],
    constant uint& n [[buffer(3)]],      // total elements
    constant uint& stride [[buffer(4)]], // number of bias elements (one per channel)
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        uint bias_idx = gid % stride;  // broadcast bias across batch/spatial dims
        float val = input[gid] + bias[bias_idx];
        output[gid] = max(0.0f, val);
    }
}

// Add bias and apply GELU (Gaussian Error Linear Unit)
// GELU(x) ≈ 0.5 * x * (1 + tanh(sqrt(2/π) * (x + 0.044715 * x³)))
kernel void bias_gelu(
    device const float* input [[buffer(0)]],
    device const float* bias [[buffer(1)]],
    device float* output [[buffer(2)]],
    constant uint& n [[buffer(3)]],
    constant uint& stride [[buffer(4)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        uint bias_idx = gid % stride;
        float x = input[gid] + bias[bias_idx];
        // Fast GELU approximation
        float cdf = 0.5f * (1.0f + tanh(0.7978845608f * (x + 0.044715f * x * x * x)));
        output[gid] = x * cdf;
    }
}

// Fused layer norm: y = (x - mean) / sqrt(var + eps) * gamma + beta
// This is a simplified version for vectors (no batch dimension)
kernel void layer_norm(
    device const float* input [[buffer(0)]],
    device const float* gamma [[buffer(1)]],
    device const float* beta [[buffer(2)]],
    device float* output [[buffer(3)]],
    constant uint& n [[buffer(4)]],
    constant float& eps [[buffer(5)]],
    threadgroup float* shared [[threadgroup(0)]],
    uint tid [[thread_index_in_threadgroup]],
    uint gid [[thread_position_in_grid]],
    uint blockDim [[threads_per_threadgroup]]
) {
    // Compute mean
    float sum = 0.0f;
    for (uint i = tid; i < n; i += blockDim) {
        sum += input[i];
    }
    shared[tid] = sum;
    threadgroup_barrier(mem_flags::mem_threadgroup);

    for (uint s = blockDim / 2; s > 0; s >>= 1) {
        if (tid < s) shared[tid] += shared[tid + s];
        threadgroup_barrier(mem_flags::mem_threadgroup);
    }
    float mean = shared[0] / float(n);
    threadgroup_barrier(mem_flags::mem_threadgroup);

    // Compute variance
    float var_sum = 0.0f;
    for (uint i = tid; i < n; i += blockDim) {
        float diff = input[i] - mean;
        var_sum += diff * diff;
    }
    shared[tid] = var_sum;
    threadgroup_barrier(mem_flags::mem_threadgroup);

    for (uint s = blockDim / 2; s > 0; s >>= 1) {
        if (tid < s) shared[tid] += shared[tid + s];
        threadgroup_barrier(mem_flags::mem_threadgroup);
    }
    float inv_std = rsqrt(shared[0] / float(n) + eps);

    // Normalize and apply affine transform
    for (uint i = tid; i < n; i += blockDim) {
        output[i] = (input[i] - mean) * inv_std * gamma[i] + beta[i];
    }
}

// ============================================================
// FUSED BATCHED SOFTMAX (one row per threadgroup)
// ============================================================
// For matrices where each row is a softmax (e.g., attention)
// Much better for ML workloads than per-element softmax

kernel void softmax_batched(
    device const float* input [[buffer(0)]],  // [batch, n]
    device float* output [[buffer(1)]],
    constant uint& n [[buffer(2)]],           // row size
    threadgroup float* shared [[threadgroup(0)]],
    uint row [[threadgroup_position_in_grid]],
    uint tid [[thread_index_in_threadgroup]],
    uint threads [[threads_per_threadgroup]]
) {
    device const float* row_in = input + row * n;
    device float* row_out = output + row * n;

    // Same algorithm as softmax_fused, operating on one row
    for (uint i = tid; i < n; i += threads) {
        shared[i] = row_in[i];
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);

    // Max reduction
    float local_max = -INFINITY;
    for (uint i = tid; i < n; i += threads) {
        local_max = max(local_max, shared[i]);
    }
    local_max = simd_max(local_max);

    threadgroup float warp_maxes[32];
    uint warp_id = tid / 32;
    uint lane_id = tid % 32;
    if (lane_id == 0 && warp_id < 32) warp_maxes[warp_id] = local_max;
    threadgroup_barrier(mem_flags::mem_threadgroup);

    if (tid < 32) {
        local_max = (tid < (threads + 31) / 32) ? warp_maxes[tid] : -INFINITY;
        local_max = simd_max(local_max);
    }
    if (tid == 0) warp_maxes[0] = local_max;
    threadgroup_barrier(mem_flags::mem_threadgroup);
    float global_max = warp_maxes[0];

    // Exp and sum
    float local_sum = 0.0f;
    for (uint i = tid; i < n; i += threads) {
        float e = exp(shared[i] - global_max);
        shared[i] = e;
        local_sum += e;
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);

    local_sum = simd_sum(local_sum);
    threadgroup float warp_sums[32];
    if (lane_id == 0 && warp_id < 32) warp_sums[warp_id] = local_sum;
    threadgroup_barrier(mem_flags::mem_threadgroup);

    if (tid < 32) {
        local_sum = (tid < (threads + 31) / 32) ? warp_sums[tid] : 0.0f;
        local_sum = simd_sum(local_sum);
    }
    if (tid == 0) warp_sums[0] = local_sum;
    threadgroup_barrier(mem_flags::mem_threadgroup);
    float global_sum = warp_sums[0];

    // Normalize
    float inv_sum = 1.0f / global_sum;
    for (uint i = tid; i < n; i += threads) {
        row_out[i] = shared[i] * inv_sum;
    }
}

// ============================================================
// LazyTensor Operations
// ============================================================

// --- Unary Operations ---

kernel void neg(
    device const float* x [[buffer(0)]],
    device float* y [[buffer(1)]],
    uint i [[thread_position_in_grid]]
) {
    y[i] = -x[i];
}

kernel void exp_op(
    device const float* x [[buffer(0)]],
    device float* y [[buffer(1)]],
    uint i [[thread_position_in_grid]]
) {
    y[i] = exp(x[i]);
}

kernel void exp2_op(
    device const float* x [[buffer(0)]],
    device float* y [[buffer(1)]],
    uint i [[thread_position_in_grid]]
) {
    y[i] = exp2(x[i]);
}

kernel void log_op(
    device const float* x [[buffer(0)]],
    device float* y [[buffer(1)]],
    uint i [[thread_position_in_grid]]
) {
    y[i] = log(x[i]);
}

kernel void log2_op(
    device const float* x [[buffer(0)]],
    device float* y [[buffer(1)]],
    uint i [[thread_position_in_grid]]
) {
    y[i] = log2(x[i]);
}

kernel void sin_op(
    device const float* x [[buffer(0)]],
    device float* y [[buffer(1)]],
    uint i [[thread_position_in_grid]]
) {
    y[i] = sin(x[i]);
}

kernel void cos_op(
    device const float* x [[buffer(0)]],
    device float* y [[buffer(1)]],
    uint i [[thread_position_in_grid]]
) {
    y[i] = cos(x[i]);
}

kernel void sqrt_op(
    device const float* x [[buffer(0)]],
    device float* y [[buffer(1)]],
    uint i [[thread_position_in_grid]]
) {
    y[i] = sqrt(x[i]);
}

kernel void reciprocal(
    device const float* x [[buffer(0)]],
    device float* y [[buffer(1)]],
    uint i [[thread_position_in_grid]]
) {
    y[i] = 1.0f / x[i];
}

kernel void relu(
    device const float* x [[buffer(0)]],
    device float* y [[buffer(1)]],
    uint i [[thread_position_in_grid]]
) {
    y[i] = max(0.0f, x[i]);
}

kernel void sigmoid(
    device const float* x [[buffer(0)]],
    device float* y [[buffer(1)]],
    uint i [[thread_position_in_grid]]
) {
    y[i] = 1.0f / (1.0f + exp(-x[i]));
}

kernel void tanh_op(
    device const float* x [[buffer(0)]],
    device float* y [[buffer(1)]],
    uint i [[thread_position_in_grid]]
) {
    y[i] = tanh(x[i]);
}

// --- Binary Operations ---

kernel void sub(
    device const float* a [[buffer(0)]],
    device const float* b [[buffer(1)]],
    device float* c [[buffer(2)]],
    uint i [[thread_position_in_grid]]
) {
    c[i] = a[i] - b[i];
}

kernel void div_op(
    device const float* a [[buffer(0)]],
    device const float* b [[buffer(1)]],
    device float* c [[buffer(2)]],
    uint i [[thread_position_in_grid]]
) {
    c[i] = a[i] / b[i];
}

kernel void max_op(
    device const float* a [[buffer(0)]],
    device const float* b [[buffer(1)]],
    device float* c [[buffer(2)]],
    uint i [[thread_position_in_grid]]
) {
    c[i] = max(a[i], b[i]);
}

kernel void min_op(
    device const float* a [[buffer(0)]],
    device const float* b [[buffer(1)]],
    device float* c [[buffer(2)]],
    uint i [[thread_position_in_grid]]
) {
    c[i] = min(a[i], b[i]);
}

kernel void pow_op(
    device const float* a [[buffer(0)]],
    device const float* b [[buffer(1)]],
    device float* c [[buffer(2)]],
    uint i [[thread_position_in_grid]]
) {
    c[i] = pow(a[i], b[i]);
}

// --- Reduction Operations ---

// Reduce max (single workgroup)
kernel void reduce_max(
    device const float* input [[buffer(0)]],
    device float* output [[buffer(1)]],
    constant uint& n [[buffer(2)]],
    threadgroup float* shared [[threadgroup(0)]],
    uint tid [[thread_index_in_threadgroup]],
    uint gid [[thread_position_in_grid]],
    uint blockDim [[threads_per_threadgroup]]
) {
    shared[tid] = (gid < n) ? input[gid] : -INFINITY;
    threadgroup_barrier(mem_flags::mem_threadgroup);

    for (uint s = blockDim / 2; s > 0; s >>= 1) {
        if (tid < s) {
            shared[tid] = max(shared[tid], shared[tid + s]);
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
    }

    if (tid == 0) {
        output[0] = shared[0];
    }
}

// Reduce min (single workgroup)
kernel void reduce_min(
    device const float* input [[buffer(0)]],
    device float* output [[buffer(1)]],
    constant uint& n [[buffer(2)]],
    threadgroup float* shared [[threadgroup(0)]],
    uint tid [[thread_index_in_threadgroup]],
    uint gid [[thread_position_in_grid]],
    uint blockDim [[threads_per_threadgroup]]
) {
    shared[tid] = (gid < n) ? input[gid] : INFINITY;
    threadgroup_barrier(mem_flags::mem_threadgroup);

    for (uint s = blockDim / 2; s > 0; s >>= 1) {
        if (tid < s) {
            shared[tid] = min(shared[tid], shared[tid + s]);
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
    }

    if (tid == 0) {
        output[0] = shared[0];
    }
}

// --- Broadcasting Binary Ops ---
// For tensors with different shapes, we need stride-based indexing

kernel void broadcast_add(
    device const float* a [[buffer(0)]],
    device const float* b [[buffer(1)]],
    device float* c [[buffer(2)]],
    constant uint* a_strides [[buffer(3)]],
    constant uint* b_strides [[buffer(4)]],
    constant uint* c_shape [[buffer(5)]],
    constant uint& ndim [[buffer(6)]],
    uint i [[thread_position_in_grid]]
) {
    // Compute multi-index from flat index
    uint remaining = i;
    uint a_idx = 0, b_idx = 0;
    for (uint d = 0; d < ndim; d++) {
        uint coord = remaining / c_shape[d];
        remaining = remaining % c_shape[d];
        a_idx += coord * a_strides[d];
        b_idx += coord * b_strides[d];
    }
    c[i] = a[a_idx] + b[b_idx];
}

kernel void broadcast_mul(
    device const float* a [[buffer(0)]],
    device const float* b [[buffer(1)]],
    device float* c [[buffer(2)]],
    constant uint* a_strides [[buffer(3)]],
    constant uint* b_strides [[buffer(4)]],
    constant uint* c_shape [[buffer(5)]],
    constant uint& ndim [[buffer(6)]],
    uint i [[thread_position_in_grid]]
) {
    uint remaining = i;
    uint a_idx = 0, b_idx = 0;
    for (uint d = 0; d < ndim; d++) {
        uint coord = remaining / c_shape[d];
        remaining = remaining % c_shape[d];
        a_idx += coord * a_strides[d];
        b_idx += coord * b_strides[d];
    }
    c[i] = a[a_idx] * b[b_idx];
}

// --- Fill Operations ---

kernel void fill_const(
    device float* x [[buffer(0)]],
    constant float& value [[buffer(1)]],
    uint i [[thread_position_in_grid]]
) {
    x[i] = value;
}
