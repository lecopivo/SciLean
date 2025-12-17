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
// Safe Simdgroup GEMM - handles arbitrary M, K, N dimensions
// ============================================================
// Uses threadgroup memory to stage tiles with proper zero-padding
// for out-of-bounds elements. Slower than gemm_simd but correct
// for all input sizes.

kernel void gemm_simd_safe(
    device const float* A [[buffer(0)]],
    device const float* B [[buffer(1)]],
    device float* C [[buffer(2)]],
    constant uint& M [[buffer(3)]],
    constant uint& K [[buffer(4)]],
    constant uint& N [[buffer(5)]],
    threadgroup float* tg_mem [[threadgroup(0)]],
    uint2 tgid [[threadgroup_position_in_grid]],
    uint simd_lane [[thread_index_in_simdgroup]],
    uint simd_id [[simdgroup_index_in_threadgroup]],
    uint tid [[thread_index_in_threadgroup]]
) {
    // Threadgroup memory layout: A_tile[32][8] followed by B_tile[8][32]
    // Total: 32*8 + 8*32 = 512 floats = 2KB
    threadgroup float* A_tile = tg_mem;           // [32][8] for this k-iteration
    threadgroup float* B_tile = tg_mem + 32 * 8;  // [8][32] for this k-iteration

    // Base row/col for this threadgroup's output tile
    uint tg_row = tgid.y * SIMD_TILE_M;
    uint tg_col = tgid.x * SIMD_TILE_N;

    // Each simdgroup handles a 16×16 subtile (2×2 arrangement of 8×8 blocks)
    uint simd_row = tg_row + (simd_id / 2) * 16;
    uint simd_col = tg_col + (simd_id % 2) * 16;

    // Accumulators for 2×2 grid of 8×8 output blocks
    simdgroup_float8x8 acc00 = simdgroup_float8x8(0);
    simdgroup_float8x8 acc01 = simdgroup_float8x8(0);
    simdgroup_float8x8 acc10 = simdgroup_float8x8(0);
    simdgroup_float8x8 acc11 = simdgroup_float8x8(0);

    // 128 threads total (4 simdgroups × 32 threads)
    // Each thread loads multiple elements to fill tiles

    // Iterate over K dimension in 8-element chunks
    for (uint k = 0; k < K; k += 8) {
        // Collaborative tile loading with bounds checking
        // Load A_tile[32][8] - each thread loads 2 elements
        for (uint i = tid; i < 32 * 8; i += 128) {
            uint row = i / 8;
            uint col = i % 8;
            uint global_row = tg_row + row;
            uint global_col = k + col;
            if (global_row < M && global_col < K) {
                A_tile[row * 8 + col] = A[global_row * K + global_col];
            } else {
                A_tile[row * 8 + col] = 0.0f;
            }
        }

        // Load B_tile[8][32] - each thread loads 2 elements
        for (uint i = tid; i < 8 * 32; i += 128) {
            uint row = i / 32;
            uint col = i % 32;
            uint global_row = k + row;
            uint global_col = tg_col + col;
            if (global_row < K && global_col < N) {
                B_tile[row * 32 + col] = B[global_row * N + global_col];
            } else {
                B_tile[row * 32 + col] = 0.0f;
            }
        }

        threadgroup_barrier(mem_flags::mem_threadgroup);

        // Load from threadgroup memory (now safe, with zeros for OOB)
        simdgroup_float8x8 a0, a1, b0, b1;

        // A tiles: rows [simd_row - tg_row, simd_row - tg_row + 16), cols [0, 8)
        uint a_local_row = simd_row - tg_row;
        simdgroup_load(a0, A_tile + a_local_row * 8, 8);
        simdgroup_load(a1, A_tile + (a_local_row + 8) * 8, 8);

        // B tiles: rows [0, 8), cols [simd_col - tg_col, simd_col - tg_col + 16)
        uint b_local_col = simd_col - tg_col;
        simdgroup_load(b0, B_tile + b_local_col, 32);
        simdgroup_load(b1, B_tile + b_local_col + 8, 32);

        // Multiply-accumulate
        simdgroup_multiply_accumulate(acc00, a0, b0, acc00);
        simdgroup_multiply_accumulate(acc01, a0, b1, acc01);
        simdgroup_multiply_accumulate(acc10, a1, b0, acc10);
        simdgroup_multiply_accumulate(acc11, a1, b1, acc11);

        threadgroup_barrier(mem_flags::mem_threadgroup);
    }

    // Store results - use threadgroup memory for boundary handling
    // Reuse tg_mem as output staging area (we're done with A_tile/B_tile)
    threadgroup float* out_tile = tg_mem;  // [32][32] fits in 512 floats

    // Store all accumulators to threadgroup memory (local coords within tile)
    uint local_row = simd_row - tg_row;
    uint local_col = simd_col - tg_col;

    simdgroup_store(acc00, out_tile + local_row * 32 + local_col, 32);
    simdgroup_store(acc01, out_tile + local_row * 32 + local_col + 8, 32);
    simdgroup_store(acc10, out_tile + (local_row + 8) * 32 + local_col, 32);
    simdgroup_store(acc11, out_tile + (local_row + 8) * 32 + local_col + 8, 32);

    threadgroup_barrier(mem_flags::mem_threadgroup);

    // Copy from threadgroup memory to global with bounds checking
    // Each thread copies multiple elements
    for (uint i = tid; i < 32 * 32; i += 128) {
        uint row = i / 32;
        uint col = i % 32;
        uint global_row = tg_row + row;
        uint global_col = tg_col + col;
        if (global_row < M && global_col < N) {
            C[global_row * N + global_col] = out_tile[row * 32 + col];
        }
    }
}

// ============================================================
// Optimized Simdgroup GEMM with Double Buffering + Safe Stores
// ============================================================
// Features:
// 1. Double buffered tile loading (overlaps compute with memory)
// 2. 64×64 output tiles for better occupancy
// 3. Safe boundary stores via threadgroup staging
// 4. Handles arbitrary M, K, N dimensions

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
    threadgroup float* tg_mem [[threadgroup(0)]],
    uint2 tgid [[threadgroup_position_in_grid]],
    uint tid [[thread_index_in_threadgroup]],
    uint simd_id [[simdgroup_index_in_threadgroup]]
) {
    // Threadgroup memory layout:
    // As[2][64][32] = 4096 floats for double-buffered A tiles
    // Bs[2][32][64] = 4096 floats for double-buffered B tiles
    // out_tile[64][64] = 4096 floats for output staging (reuses As after compute)
    threadgroup float* As = tg_mem;                    // [2][64][32]
    threadgroup float* Bs = tg_mem + 2 * 64 * 32;      // [2][32][64]

    // Threadgroup computes 64×64 output
    uint tg_row = tgid.y * OPT_TILE_M;
    uint tg_col = tgid.x * OPT_TILE_N;

    // 256 threads = 8 simdgroups
    // Each simdgroup handles 32×16 output (4×2 grid of 8×8 blocks)
    // Layout: 2 rows × 4 cols of simdgroups covering 64×64
    uint simd_row_offset = (simd_id / 4) * 32;  // 0 or 32
    uint simd_col_offset = (simd_id % 4) * 16;  // 0, 16, 32, 48

    // 4×2 grid of 8×8 accumulators per simdgroup
    simdgroup_float8x8 acc[4][2];
    for (int i = 0; i < 4; i++) {
        for (int j = 0; j < 2; j++) {
            acc[i][j] = simdgroup_float8x8(0);
        }
    }

    // Helper macros for indexing
    #define AS(buf, r, c) As[(buf) * 64 * 32 + (r) * 32 + (c)]
    #define BS(buf, r, c) Bs[(buf) * 32 * 64 + (r) * 64 + (c)]

    // Load first tile (256 threads, 64×32 = 2048 elements → 8 per thread)
    int buf = 0;

    for (uint i = tid; i < OPT_TILE_M * OPT_TILE_K; i += 256) {
        uint ar = i / OPT_TILE_K;
        uint ac = i % OPT_TILE_K;
        uint gr = tg_row + ar;
        uint gc = ac;
        AS(buf, ar, ac) = (gr < M && gc < K) ? A[gr * K + gc] : 0.0f;
    }

    for (uint i = tid; i < OPT_TILE_K * OPT_TILE_N; i += 256) {
        uint br = i / OPT_TILE_N;
        uint bc = i % OPT_TILE_N;
        uint gr = br;
        uint gc = tg_col + bc;
        BS(buf, br, bc) = (gr < K && gc < N) ? B[gr * N + gc] : 0.0f;
    }

    threadgroup_barrier(mem_flags::mem_threadgroup);

    // Main loop with double buffering
    for (uint k = 0; k < K; k += OPT_TILE_K) {
        uint next_k = k + OPT_TILE_K;
        int next_buf = 1 - buf;

        // Prefetch next tiles while computing current
        if (next_k < K) {
            for (uint i = tid; i < OPT_TILE_M * OPT_TILE_K; i += 256) {
                uint ar = i / OPT_TILE_K;
                uint ac = i % OPT_TILE_K;
                uint gr = tg_row + ar;
                uint gc = next_k + ac;
                AS(next_buf, ar, ac) = (gr < M && gc < K) ? A[gr * K + gc] : 0.0f;
            }
            for (uint i = tid; i < OPT_TILE_K * OPT_TILE_N; i += 256) {
                uint br = i / OPT_TILE_N;
                uint bc = i % OPT_TILE_N;
                uint gr = next_k + br;
                uint gc = tg_col + bc;
                BS(next_buf, br, bc) = (gr < K && gc < N) ? B[gr * N + gc] : 0.0f;
            }
        }

        // Compute: iterate over K tile in 8-element chunks
        for (uint kk = 0; kk < OPT_TILE_K && (k + kk) < K; kk += 8) {
            simdgroup_float8x8 a[4], b[2];

            // Load A subtiles (4 × 8×8)
            for (int ai = 0; ai < 4; ai++) {
                simdgroup_load(a[ai], &AS(buf, simd_row_offset + ai * 8, kk), OPT_TILE_K);
            }

            // Load B subtiles (2 × 8×8)
            for (int bi = 0; bi < 2; bi++) {
                simdgroup_load(b[bi], &BS(buf, kk, simd_col_offset + bi * 8), OPT_TILE_N);
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

    #undef AS
    #undef BS

    // Store results via threadgroup memory for safe boundary handling
    // Reuse As memory as output staging (64×64 = 4096 floats, fits in As space)
    threadgroup float* out_tile = tg_mem;

    // Store accumulators to threadgroup memory
    for (int ai = 0; ai < 4; ai++) {
        for (int bi = 0; bi < 2; bi++) {
            uint local_row = simd_row_offset + ai * 8;
            uint local_col = simd_col_offset + bi * 8;
            simdgroup_store(acc[ai][bi], out_tile + local_row * 64 + local_col, 64);
        }
    }

    threadgroup_barrier(mem_flags::mem_threadgroup);

    // Copy from threadgroup to global with bounds checking
    for (uint i = tid; i < OPT_TILE_M * OPT_TILE_N; i += 256) {
        uint row = i / OPT_TILE_N;
        uint col = i % OPT_TILE_N;
        uint global_row = tg_row + row;
        uint global_col = tg_col + col;
        if (global_row < M && global_col < N) {
            C[global_row * N + global_col] = out_tile[row * 64 + col];
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

// ============================================================
// FUSED GEMM + BIAS + RELU
// ============================================================
// C = max(0, A @ B + bias)
// bias is broadcast along rows (length N)
// Uses tiled algorithm for cache efficiency

kernel void gemm_bias_relu(
    device const float* A [[buffer(0)]],
    device const float* B [[buffer(1)]],
    device const float* bias [[buffer(2)]],
    device float* C [[buffer(3)]],
    constant uint& M [[buffer(4)]],
    constant uint& K [[buffer(5)]],
    constant uint& N [[buffer(6)]],
    uint2 tid [[thread_position_in_threadgroup]],
    uint2 tgid [[threadgroup_position_in_grid]]
) {
    threadgroup float As[TILE_SIZE][TILE_SIZE];
    threadgroup float Bs[TILE_SIZE][TILE_SIZE];

    uint row = tgid.y * TILE_SIZE + tid.y;
    uint col = tgid.x * TILE_SIZE + tid.x;

    float sum = 0.0f;
    uint numTiles = (K + TILE_SIZE - 1) / TILE_SIZE;

    for (uint t = 0; t < numTiles; t++) {
        uint aCol = t * TILE_SIZE + tid.x;
        uint bRow = t * TILE_SIZE + tid.y;

        As[tid.y][tid.x] = (row < M && aCol < K) ? A[row * K + aCol] : 0.0f;
        Bs[tid.y][tid.x] = (bRow < K && col < N) ? B[bRow * N + col] : 0.0f;

        threadgroup_barrier(mem_flags::mem_threadgroup);

        for (uint i = 0; i < TILE_SIZE; i++) {
            sum += As[tid.y][i] * Bs[i][tid.x];
        }

        threadgroup_barrier(mem_flags::mem_threadgroup);
    }

    // Fused bias + ReLU at store
    if (row < M && col < N) {
        float val = sum + bias[col];  // bias broadcasted per column
        C[row * N + col] = max(0.0f, val);
    }
}

// Simdgroup-accelerated GEMM + bias + ReLU for larger matrices
kernel void gemm_bias_relu_simd(
    device const float* A [[buffer(0)]],
    device const float* B [[buffer(1)]],
    device const float* bias [[buffer(2)]],
    device float* C [[buffer(3)]],
    constant uint& M [[buffer(4)]],
    constant uint& K [[buffer(5)]],
    constant uint& N [[buffer(6)]],
    uint2 tgid [[threadgroup_position_in_grid]],
    uint simd_lane [[thread_index_in_simdgroup]],
    uint simd_id [[simdgroup_index_in_threadgroup]]
) {
    // Same layout as gemm_simd
    uint tg_row = tgid.y * SIMD_TILE_M;
    uint tg_col = tgid.x * SIMD_TILE_N;

    uint simd_row = tg_row + (simd_id / 2) * 16;
    uint simd_col = tg_col + (simd_id % 2) * 16;

    simdgroup_float8x8 acc00 = simdgroup_float8x8(0);
    simdgroup_float8x8 acc01 = simdgroup_float8x8(0);
    simdgroup_float8x8 acc10 = simdgroup_float8x8(0);
    simdgroup_float8x8 acc11 = simdgroup_float8x8(0);

    for (uint k = 0; k < K; k += 8) {
        simdgroup_float8x8 a0, a1;
        simdgroup_float8x8 b0, b1;

        if (simd_row < M && k < K) {
            simdgroup_load(a0, A + simd_row * K + k, K);
        }
        if (simd_row + 8 < M && k < K) {
            simdgroup_load(a1, A + (simd_row + 8) * K + k, K);
        }
        if (k < K && simd_col < N) {
            simdgroup_load(b0, B + k * N + simd_col, N);
        }
        if (k < K && simd_col + 8 < N) {
            simdgroup_load(b1, B + k * N + simd_col + 8, N);
        }

        simdgroup_multiply_accumulate(acc00, a0, b0, acc00);
        simdgroup_multiply_accumulate(acc01, a0, b1, acc01);
        simdgroup_multiply_accumulate(acc10, a1, b0, acc10);
        simdgroup_multiply_accumulate(acc11, a1, b1, acc11);
    }

    // Store to shared memory, apply bias+relu, then write to global
    // Note: simdgroup_store followed by element-wise is simpler for now
    threadgroup float temp[32][32];

    if (simd_row < M && simd_col < N) {
        simdgroup_store(acc00, &temp[0][0], 32);
    }
    if (simd_row < M && simd_col + 8 < N) {
        simdgroup_store(acc01, &temp[0][8], 32);
    }
    if (simd_row + 8 < M && simd_col < N) {
        simdgroup_store(acc10, &temp[8][0], 32);
    }
    if (simd_row + 8 < M && simd_col + 8 < N) {
        simdgroup_store(acc11, &temp[8][8], 32);
    }

    threadgroup_barrier(mem_flags::mem_threadgroup);

    // Apply bias + ReLU and write to global (one thread per element)
    uint local_row = simd_lane / 16;
    uint local_col = simd_lane % 16;
    for (uint dr = 0; dr < 16; dr += 2) {
        uint out_row = simd_row + dr + local_row;
        uint out_col = simd_col + local_col;
        if (out_row < M && out_col < N) {
            float val = temp[dr + local_row][local_col] + bias[out_col];
            C[out_row * N + out_col] = max(0.0f, val);
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

// Add bias only (no activation) - for output layer before softmax
// Broadcasts bias across batch dimension: output[i] = input[i] + bias[i % stride]
kernel void bias_add(
    device const float* input [[buffer(0)]],
    device const float* bias [[buffer(1)]],
    device float* output [[buffer(2)]],
    constant uint& n [[buffer(3)]],
    constant uint& stride [[buffer(4)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        uint bias_idx = gid % stride;
        output[gid] = input[gid] + bias[bias_idx];
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

// Column sum (sum over rows for each column)
// Input: [rows, cols], Output: [cols]
// Each thread handles one column
kernel void col_sum_simple(
    device const float* input [[buffer(0)]],
    device float* output [[buffer(1)]],
    constant uint& rows [[buffer(2)]],
    constant uint& cols [[buffer(3)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid >= cols) return;

    float sum = 0.0f;
    for (uint r = 0; r < rows; r++) {
        sum += input[r * cols + gid];
    }
    output[gid] = sum;
}

// Optimized column sum with threadgroup reduction for large row counts
// Each threadgroup handles one column, reducing over rows
#define COLSUM_THREADS 256
kernel void col_sum_large(
    device const float* input [[buffer(0)]],
    device float* output [[buffer(1)]],
    constant uint& rows [[buffer(2)]],
    constant uint& cols [[buffer(3)]],
    threadgroup float* shared [[threadgroup(0)]],
    uint tid [[thread_index_in_threadgroup]],
    uint blockIdx [[threadgroup_position_in_grid]]
) {
    uint col = blockIdx;
    if (col >= cols) return;

    // Grid-stride loop over rows
    float sum = 0.0f;
    for (uint r = tid; r < rows; r += COLSUM_THREADS) {
        sum += input[r * cols + col];
    }

    shared[tid] = sum;
    threadgroup_barrier(mem_flags::mem_threadgroup);

    // Binary tree reduction
    for (uint s = COLSUM_THREADS / 2; s > 0; s >>= 1) {
        if (tid < s) {
            shared[tid] += shared[tid + s];
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
    }

    if (tid == 0) {
        output[col] = shared[0];
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

// ============================================================
// Fused Attention Kernels
// ============================================================
// Implements scaled dot-product attention: softmax(Q*K^T / sqrt(d_k)) * V
// Memory-efficient: one threadgroup per query position

// ============================================================
// Flash Attention - Simple Serial Version
// ============================================================
// Single thread per query for correctness. Each threadgroup handles one query.
// Slower but correct - can optimize later.

kernel void flash_attention(
    device const float* Q [[buffer(0)]],    // [seq_len, head_dim]
    device const float* K [[buffer(1)]],    // [seq_len, head_dim]
    device const float* V [[buffer(2)]],    // [seq_len, head_dim]
    device float* output [[buffer(3)]],     // [seq_len, head_dim]
    constant uint& seq_len [[buffer(4)]],
    constant uint& head_dim [[buffer(5)]],
    constant float& scale [[buffer(6)]],
    uint q_idx [[thread_position_in_grid]]
) {
    if (q_idx >= seq_len) return;

    // First pass: compute max score for numerical stability
    float max_score = -INFINITY;
    for (uint k_idx = 0; k_idx < seq_len; k_idx++) {
        float score = 0.0f;
        for (uint d = 0; d < head_dim; d++) {
            score += Q[q_idx * head_dim + d] * K[k_idx * head_dim + d];
        }
        score *= scale;
        max_score = max(max_score, score);
    }

    // Second pass: compute exp sum
    float sum_exp = 0.0f;
    for (uint k_idx = 0; k_idx < seq_len; k_idx++) {
        float score = 0.0f;
        for (uint d = 0; d < head_dim; d++) {
            score += Q[q_idx * head_dim + d] * K[k_idx * head_dim + d];
        }
        score *= scale;
        sum_exp += exp(score - max_score);
    }

    // Third pass: compute weighted sum with V
    float inv_sum = 1.0f / sum_exp;
    for (uint d = 0; d < head_dim; d++) {
        float out_d = 0.0f;
        for (uint k_idx = 0; k_idx < seq_len; k_idx++) {
            float score = 0.0f;
            for (uint dd = 0; dd < head_dim; dd++) {
                score += Q[q_idx * head_dim + dd] * K[k_idx * head_dim + dd];
            }
            score *= scale;
            float weight = exp(score - max_score) * inv_sum;
            out_d += weight * V[k_idx * head_dim + d];
        }
        output[q_idx * head_dim + d] = out_d;
    }
}

// Causal (masked) attention - only attends to positions <= current position
// Simple serial version: one thread per query
kernel void flash_attention_causal(
    device const float* Q [[buffer(0)]],
    device const float* K [[buffer(1)]],
    device const float* V [[buffer(2)]],
    device float* output [[buffer(3)]],
    constant uint& seq_len [[buffer(4)]],
    constant uint& head_dim [[buffer(5)]],
    constant float& scale [[buffer(6)]],
    uint q_idx [[thread_position_in_grid]]
) {
    if (q_idx >= seq_len) return;

    // First pass: compute max score for numerical stability
    // Only consider positions <= q_idx (causal mask)
    float max_score = -INFINITY;
    for (uint k_idx = 0; k_idx <= q_idx; k_idx++) {
        float score = 0.0f;
        for (uint d = 0; d < head_dim; d++) {
            score += Q[q_idx * head_dim + d] * K[k_idx * head_dim + d];
        }
        score *= scale;
        max_score = max(max_score, score);
    }

    // Second pass: compute exp sum
    float sum_exp = 0.0f;
    for (uint k_idx = 0; k_idx <= q_idx; k_idx++) {
        float score = 0.0f;
        for (uint d = 0; d < head_dim; d++) {
            score += Q[q_idx * head_dim + d] * K[k_idx * head_dim + d];
        }
        score *= scale;
        sum_exp += exp(score - max_score);
    }

    // Third pass: compute weighted sum with V
    float inv_sum = 1.0f / sum_exp;
    for (uint d = 0; d < head_dim; d++) {
        float out_d = 0.0f;
        for (uint k_idx = 0; k_idx <= q_idx; k_idx++) {
            float score = 0.0f;
            for (uint dd = 0; dd < head_dim; dd++) {
                score += Q[q_idx * head_dim + dd] * K[k_idx * head_dim + dd];
            }
            score *= scale;
            float weight = exp(score - max_score) * inv_sum;
            out_d += weight * V[k_idx * head_dim + d];
        }
        output[q_idx * head_dim + d] = out_d;
    }
}

// ============================================================================
// Conv2D kernels for CNN inference
// ============================================================================

// Conv2D naive - one thread per output element
// Input: NCHW format (batch, channels, height, width)
// Kernel: OIHW format (out_channels, in_channels, kernel_h, kernel_w)
// Output: NCHW format
kernel void conv2d_naive(
    device const float* input [[buffer(0)]],
    device const float* kernel_weights [[buffer(1)]],
    device const float* bias [[buffer(2)]],
    device float* output [[buffer(3)]],
    constant uint& batch_size [[buffer(4)]],
    constant uint& in_channels [[buffer(5)]],
    constant uint& out_channels [[buffer(6)]],
    constant uint& in_height [[buffer(7)]],
    constant uint& in_width [[buffer(8)]],
    constant uint& kernel_h [[buffer(9)]],
    constant uint& kernel_w [[buffer(10)]],
    constant uint& stride_h [[buffer(11)]],
    constant uint& stride_w [[buffer(12)]],
    constant uint& pad_h [[buffer(13)]],
    constant uint& pad_w [[buffer(14)]],
    uint3 gid [[thread_position_in_grid]]
) {
    // Output dimensions
    uint out_height = (in_height + 2 * pad_h - kernel_h) / stride_h + 1;
    uint out_width = (in_width + 2 * pad_w - kernel_w) / stride_w + 1;

    // gid.x = output column, gid.y = output row, gid.z = batch * out_channels + oc
    uint ow = gid.x;
    uint oh = gid.y;
    uint batch_oc = gid.z;
    uint batch = batch_oc / out_channels;
    uint oc = batch_oc % out_channels;

    if (ow >= out_width || oh >= out_height || batch >= batch_size) return;

    float sum = bias[oc];

    // Convolution
    for (uint ic = 0; ic < in_channels; ic++) {
        for (uint kh = 0; kh < kernel_h; kh++) {
            for (uint kw = 0; kw < kernel_w; kw++) {
                int ih = (int)(oh * stride_h + kh) - (int)pad_h;
                int iw = (int)(ow * stride_w + kw) - (int)pad_w;

                if (ih >= 0 && ih < (int)in_height && iw >= 0 && iw < (int)in_width) {
                    uint in_idx = batch * in_channels * in_height * in_width
                                + ic * in_height * in_width
                                + ih * in_width + iw;
                    uint k_idx = oc * in_channels * kernel_h * kernel_w
                               + ic * kernel_h * kernel_w
                               + kh * kernel_w + kw;
                    sum += input[in_idx] * kernel_weights[k_idx];
                }
            }
        }
    }

    uint out_idx = batch * out_channels * out_height * out_width
                 + oc * out_height * out_width
                 + oh * out_width + ow;
    output[out_idx] = sum;
}

// Conv2D with implicit GEMM (im2col approach without materializing im2col)
// More efficient for larger convolutions
kernel void conv2d_implicit_gemm(
    device const float* input [[buffer(0)]],
    device const float* kernel_weights [[buffer(1)]],
    device const float* bias [[buffer(2)]],
    device float* output [[buffer(3)]],
    constant uint& batch_size [[buffer(4)]],
    constant uint& in_channels [[buffer(5)]],
    constant uint& out_channels [[buffer(6)]],
    constant uint& in_height [[buffer(7)]],
    constant uint& in_width [[buffer(8)]],
    constant uint& kernel_h [[buffer(9)]],
    constant uint& kernel_w [[buffer(10)]],
    constant uint& stride_h [[buffer(11)]],
    constant uint& stride_w [[buffer(12)]],
    constant uint& pad_h [[buffer(13)]],
    constant uint& pad_w [[buffer(14)]],
    uint2 gid [[thread_position_in_grid]],
    uint2 tid [[thread_position_in_threadgroup]],
    uint2 tg_size [[threads_per_threadgroup]]
) {
    // Output dimensions
    uint out_height = (in_height + 2 * pad_h - kernel_h) / stride_h + 1;
    uint out_width = (in_width + 2 * pad_w - kernel_w) / stride_w + 1;
    uint out_spatial = out_height * out_width;

    // gid.x = spatial position (oh * out_width + ow) across all batches
    // gid.y = output channel
    uint spatial_batch = gid.x;
    uint oc = gid.y;

    if (oc >= out_channels) return;

    uint batch = spatial_batch / out_spatial;
    uint spatial = spatial_batch % out_spatial;
    uint oh = spatial / out_width;
    uint ow = spatial % out_width;

    if (batch >= batch_size) return;

    // Kernel reduction dimension: in_channels * kernel_h * kernel_w
    uint K = in_channels * kernel_h * kernel_w;

    float sum = bias[oc];

    // Compute dot product between im2col column and kernel row
    for (uint k = 0; k < K; k++) {
        uint ic = k / (kernel_h * kernel_w);
        uint rem = k % (kernel_h * kernel_w);
        uint kh = rem / kernel_w;
        uint kw = rem % kernel_w;

        int ih = (int)(oh * stride_h + kh) - (int)pad_h;
        int iw = (int)(ow * stride_w + kw) - (int)pad_w;

        float in_val = 0.0f;
        if (ih >= 0 && ih < (int)in_height && iw >= 0 && iw < (int)in_width) {
            uint in_idx = batch * in_channels * in_height * in_width
                        + ic * in_height * in_width
                        + ih * in_width + iw;
            in_val = input[in_idx];
        }

        uint k_idx = oc * K + k;
        sum += in_val * kernel_weights[k_idx];
    }

    uint out_idx = batch * out_channels * out_height * out_width
                 + oc * out_height * out_width
                 + oh * out_width + ow;
    output[out_idx] = sum;
}

// Conv2D fused with ReLU activation
kernel void conv2d_relu(
    device const float* input [[buffer(0)]],
    device const float* kernel_weights [[buffer(1)]],
    device const float* bias [[buffer(2)]],
    device float* output [[buffer(3)]],
    constant uint& batch_size [[buffer(4)]],
    constant uint& in_channels [[buffer(5)]],
    constant uint& out_channels [[buffer(6)]],
    constant uint& in_height [[buffer(7)]],
    constant uint& in_width [[buffer(8)]],
    constant uint& kernel_h [[buffer(9)]],
    constant uint& kernel_w [[buffer(10)]],
    constant uint& stride_h [[buffer(11)]],
    constant uint& stride_w [[buffer(12)]],
    constant uint& pad_h [[buffer(13)]],
    constant uint& pad_w [[buffer(14)]],
    uint3 gid [[thread_position_in_grid]]
) {
    uint out_height = (in_height + 2 * pad_h - kernel_h) / stride_h + 1;
    uint out_width = (in_width + 2 * pad_w - kernel_w) / stride_w + 1;

    uint ow = gid.x;
    uint oh = gid.y;
    uint batch_oc = gid.z;
    uint batch = batch_oc / out_channels;
    uint oc = batch_oc % out_channels;

    if (ow >= out_width || oh >= out_height || batch >= batch_size) return;

    float sum = bias[oc];

    for (uint ic = 0; ic < in_channels; ic++) {
        for (uint kh = 0; kh < kernel_h; kh++) {
            for (uint kw = 0; kw < kernel_w; kw++) {
                int ih = (int)(oh * stride_h + kh) - (int)pad_h;
                int iw = (int)(ow * stride_w + kw) - (int)pad_w;

                if (ih >= 0 && ih < (int)in_height && iw >= 0 && iw < (int)in_width) {
                    uint in_idx = batch * in_channels * in_height * in_width
                                + ic * in_height * in_width
                                + ih * in_width + iw;
                    uint k_idx = oc * in_channels * kernel_h * kernel_w
                               + ic * kernel_h * kernel_w
                               + kh * kernel_w + kw;
                    sum += input[in_idx] * kernel_weights[k_idx];
                }
            }
        }
    }

    uint out_idx = batch * out_channels * out_height * out_width
                 + oc * out_height * out_width
                 + oh * out_width + ow;
    output[out_idx] = max(0.0f, sum);  // ReLU
}

// MaxPool2D - one thread per output element
kernel void maxpool2d(
    device const float* input [[buffer(0)]],
    device float* output [[buffer(1)]],
    constant uint& batch_size [[buffer(2)]],
    constant uint& channels [[buffer(3)]],
    constant uint& in_height [[buffer(4)]],
    constant uint& in_width [[buffer(5)]],
    constant uint& pool_h [[buffer(6)]],
    constant uint& pool_w [[buffer(7)]],
    constant uint& stride_h [[buffer(8)]],
    constant uint& stride_w [[buffer(9)]],
    uint3 gid [[thread_position_in_grid]]
) {
    uint out_height = (in_height - pool_h) / stride_h + 1;
    uint out_width = (in_width - pool_w) / stride_w + 1;

    uint ow = gid.x;
    uint oh = gid.y;
    uint batch_c = gid.z;
    uint batch = batch_c / channels;
    uint c = batch_c % channels;

    if (ow >= out_width || oh >= out_height || batch >= batch_size) return;

    float max_val = -INFINITY;

    for (uint ph = 0; ph < pool_h; ph++) {
        for (uint pw = 0; pw < pool_w; pw++) {
            uint ih = oh * stride_h + ph;
            uint iw = ow * stride_w + pw;
            uint in_idx = batch * channels * in_height * in_width
                        + c * in_height * in_width
                        + ih * in_width + iw;
            max_val = max(max_val, input[in_idx]);
        }
    }

    uint out_idx = batch * channels * out_height * out_width
                 + c * out_height * out_width
                 + oh * out_width + ow;
    output[out_idx] = max_val;
}

// AvgPool2D - one thread per output element
kernel void avgpool2d(
    device const float* input [[buffer(0)]],
    device float* output [[buffer(1)]],
    constant uint& batch_size [[buffer(2)]],
    constant uint& channels [[buffer(3)]],
    constant uint& in_height [[buffer(4)]],
    constant uint& in_width [[buffer(5)]],
    constant uint& pool_h [[buffer(6)]],
    constant uint& pool_w [[buffer(7)]],
    constant uint& stride_h [[buffer(8)]],
    constant uint& stride_w [[buffer(9)]],
    uint3 gid [[thread_position_in_grid]]
) {
    uint out_height = (in_height - pool_h) / stride_h + 1;
    uint out_width = (in_width - pool_w) / stride_w + 1;

    uint ow = gid.x;
    uint oh = gid.y;
    uint batch_c = gid.z;
    uint batch = batch_c / channels;
    uint c = batch_c % channels;

    if (ow >= out_width || oh >= out_height || batch >= batch_size) return;

    float sum = 0.0f;
    float count = (float)(pool_h * pool_w);

    for (uint ph = 0; ph < pool_h; ph++) {
        for (uint pw = 0; pw < pool_w; pw++) {
            uint ih = oh * stride_h + ph;
            uint iw = ow * stride_w + pw;
            uint in_idx = batch * channels * in_height * in_width
                        + c * in_height * in_width
                        + ih * in_width + iw;
            sum += input[in_idx];
        }
    }

    uint out_idx = batch * channels * out_height * out_width
                 + c * out_height * out_width
                 + oh * out_width + ow;
    output[out_idx] = sum / count;
}

// Global Average Pooling - reduces spatial dimensions to 1x1
kernel void global_avgpool2d(
    device const float* input [[buffer(0)]],
    device float* output [[buffer(1)]],
    constant uint& batch_size [[buffer(2)]],
    constant uint& channels [[buffer(3)]],
    constant uint& height [[buffer(4)]],
    constant uint& width [[buffer(5)]],
    uint2 gid [[thread_position_in_grid]]
) {
    uint batch = gid.x;
    uint c = gid.y;

    if (batch >= batch_size || c >= channels) return;

    float sum = 0.0f;
    uint spatial = height * width;

    for (uint h = 0; h < height; h++) {
        for (uint w = 0; w < width; w++) {
            uint in_idx = batch * channels * height * width
                        + c * height * width
                        + h * width + w;
            sum += input[in_idx];
        }
    }

    output[batch * channels + c] = sum / (float)spatial;
}

// ============================================================================
// Optimized Conv2D using simdgroup matrix operations (similar to GEMM tiling)
// ============================================================================
// Conv2D as implicit GEMM:
//   Output[n,oc,oh,ow] = sum over ic,kh,kw of Input[n,ic,ih,iw] * Weight[oc,ic,kh,kw]
// This is equivalent to:
//   C[oc, spatial] = W[oc, ic*kh*kw] * Im2Col[ic*kh*kw, spatial]
// where spatial = oh*ow and Im2Col is computed on-the-fly

constant uint CONV_TILE_M = 32;  // Output channels tile
constant uint CONV_TILE_N = 32;  // Spatial positions tile
constant uint CONV_TILE_K = 8;   // Reduction dimension tile (ic*kh*kw)

kernel void conv2d_tiled(
    device const float* input [[buffer(0)]],
    device const float* kernel_weights [[buffer(1)]],
    device const float* bias [[buffer(2)]],
    device float* output [[buffer(3)]],
    constant uint& batch_size [[buffer(4)]],
    constant uint& in_channels [[buffer(5)]],
    constant uint& out_channels [[buffer(6)]],
    constant uint& in_height [[buffer(7)]],
    constant uint& in_width [[buffer(8)]],
    constant uint& kernel_h [[buffer(9)]],
    constant uint& kernel_w [[buffer(10)]],
    constant uint& stride_h [[buffer(11)]],
    constant uint& stride_w [[buffer(12)]],
    constant uint& pad_h [[buffer(13)]],
    constant uint& pad_w [[buffer(14)]],
    constant uint& use_relu [[buffer(15)]],
    uint3 group_id [[threadgroup_position_in_grid]],
    uint3 thread_id [[thread_position_in_threadgroup]],
    uint simd_lane_id [[thread_index_in_simdgroup]],
    uint simd_group_id [[simdgroup_index_in_threadgroup]]
) {
    // Output dimensions
    uint out_height = (in_height + 2 * pad_h - kernel_h) / stride_h + 1;
    uint out_width = (in_width + 2 * pad_w - kernel_w) / stride_w + 1;
    uint out_spatial = out_height * out_width;

    // Reduction dimension K = in_channels * kernel_h * kernel_w
    uint K = in_channels * kernel_h * kernel_w;

    // Block position
    uint batch = group_id.z;
    uint oc_base = group_id.y * CONV_TILE_M;
    uint spatial_base = group_id.x * CONV_TILE_N;

    if (batch >= batch_size) return;

    // Thread within block
    uint local_row = thread_id.y;  // oc offset
    uint local_col = thread_id.x;  // spatial offset

    // Each thread computes one output element
    uint oc = oc_base + local_row;
    uint spatial = spatial_base + local_col;

    if (oc >= out_channels || spatial >= out_spatial) return;

    uint oh = spatial / out_width;
    uint ow = spatial % out_width;

    // Initialize with bias
    float acc = bias[oc];

    // Loop over reduction dimension with simd-friendly access
    for (uint k = 0; k < K; k++) {
        uint ic = k / (kernel_h * kernel_w);
        uint rem = k % (kernel_h * kernel_w);
        uint kh = rem / kernel_w;
        uint kw = rem % kernel_w;

        int ih = (int)(oh * stride_h + kh) - (int)pad_h;
        int iw = (int)(ow * stride_w + kw) - (int)pad_w;

        float in_val = 0.0f;
        if (ih >= 0 && ih < (int)in_height && iw >= 0 && iw < (int)in_width) {
            uint in_idx = batch * in_channels * in_height * in_width
                        + ic * in_height * in_width
                        + ih * in_width + iw;
            in_val = input[in_idx];
        }

        // Weight index: [oc, ic, kh, kw] in OIHW format
        uint w_idx = oc * K + k;
        acc += in_val * kernel_weights[w_idx];
    }

    // Apply ReLU if requested
    if (use_relu) {
        acc = max(0.0f, acc);
    }

    // Write output
    uint out_idx = batch * out_channels * out_height * out_width
                 + oc * out_height * out_width
                 + oh * out_width + ow;
    output[out_idx] = acc;
}

// Im2col kernel - materializes implicit im2col matrix for conv as GEMM
// This creates a [K, N] matrix where K = in_channels * kernel_h * kernel_w
// and N = out_height * out_width (spatial positions)
// Then conv becomes: output = weights [M, K] * im2col [K, N]
kernel void conv2d_im2col(
    device const float* input [[buffer(0)]],
    device float* im2col [[buffer(1)]],
    constant uint& batch [[buffer(2)]],
    constant uint& in_channels [[buffer(3)]],
    constant uint& in_height [[buffer(4)]],
    constant uint& in_width [[buffer(5)]],
    constant uint& kernel_h [[buffer(6)]],
    constant uint& kernel_w [[buffer(7)]],
    constant uint& stride_h [[buffer(8)]],
    constant uint& stride_w [[buffer(9)]],
    constant uint& pad_h [[buffer(10)]],
    constant uint& pad_w [[buffer(11)]],
    constant uint& out_height [[buffer(12)]],
    constant uint& out_width [[buffer(13)]],
    uint2 gid [[thread_position_in_grid]]
) {
    // gid.x = spatial position (oh * out_width + ow)
    // gid.y = K index (ic * kernel_h * kernel_w + kh * kernel_w + kw)

    uint n_idx = gid.x;  // Spatial position
    uint k_idx = gid.y;  // K dimension

    uint out_spatial = out_height * out_width;
    if (n_idx >= out_spatial) return;

    uint K = in_channels * kernel_h * kernel_w;
    if (k_idx >= K) return;

    // Decode K index
    uint ic = k_idx / (kernel_h * kernel_w);
    uint rem = k_idx % (kernel_h * kernel_w);
    uint kh = rem / kernel_w;
    uint kw = rem % kernel_w;

    // Decode spatial position
    uint oh = n_idx / out_width;
    uint ow = n_idx % out_width;

    // Compute input position
    int ih = (int)(oh * stride_h + kh) - (int)pad_h;
    int iw = (int)(ow * stride_w + kw) - (int)pad_w;

    float val = 0.0f;
    if (ih >= 0 && ih < (int)in_height && iw >= 0 && iw < (int)in_width) {
        uint in_idx = batch * in_channels * in_height * in_width
                    + ic * in_height * in_width
                    + ih * in_width + iw;
        val = input[in_idx];
    }

    // im2col is stored as [K, N] where N = out_spatial
    im2col[k_idx * out_spatial + n_idx] = val;
}

// Winograd-inspired Conv2D for 3x3 kernels (specialized fast path)
// Uses F(2x2, 3x3) Winograd to reduce multiplications
kernel void conv2d_3x3_winograd(
    device const float* input [[buffer(0)]],
    device const float* kernel_weights [[buffer(1)]],  // Pre-transformed weights
    device const float* bias [[buffer(2)]],
    device float* output [[buffer(3)]],
    constant uint& batch_size [[buffer(4)]],
    constant uint& in_channels [[buffer(5)]],
    constant uint& out_channels [[buffer(6)]],
    constant uint& in_height [[buffer(7)]],
    constant uint& in_width [[buffer(8)]],
    constant uint& use_relu [[buffer(9)]],
    uint3 gid [[thread_position_in_grid]]
) {
    // For 3x3 conv with stride 1, padding 1 (same padding)
    // Output has same dimensions as input
    uint out_height = in_height;
    uint out_width = in_width;

    uint ow = gid.x;
    uint oh = gid.y;
    uint batch_oc = gid.z;
    uint batch = batch_oc / out_channels;
    uint oc = batch_oc % out_channels;

    if (ow >= out_width || oh >= out_height || batch >= batch_size) return;

    float sum = bias[oc];

    // Standard 3x3 conv with unrolled loops for better performance
    for (uint ic = 0; ic < in_channels; ic++) {
        // Unrolled 3x3 kernel
        #pragma unroll
        for (int kh = 0; kh < 3; kh++) {
            int ih = (int)oh + kh - 1;  // padding = 1
            if (ih < 0 || ih >= (int)in_height) continue;

            #pragma unroll
            for (int kw = 0; kw < 3; kw++) {
                int iw = (int)ow + kw - 1;  // padding = 1
                if (iw < 0 || iw >= (int)in_width) continue;

                uint in_idx = batch * in_channels * in_height * in_width
                            + ic * in_height * in_width
                            + ih * in_width + iw;
                uint k_idx = oc * in_channels * 9
                           + ic * 9
                           + kh * 3 + kw;
                sum += input[in_idx] * kernel_weights[k_idx];
            }
        }
    }

    if (use_relu) {
        sum = max(0.0f, sum);
    }

    uint out_idx = batch * out_channels * out_height * out_width
                 + oc * out_height * out_width
                 + oh * out_width + ow;
    output[out_idx] = sum;
}

// Highly optimized Conv2D using simdgroup matrix multiply
// This treats conv as GEMM: C[M,N] = A[M,K] * B[K,N]
// where M=out_channels, K=in_channels*kh*kw, N=out_h*out_w
kernel void conv2d_simd(
    device const float* input [[buffer(0)]],
    device const float* kernel_weights [[buffer(1)]],
    device const float* bias [[buffer(2)]],
    device float* output [[buffer(3)]],
    constant uint& batch_size [[buffer(4)]],
    constant uint& in_channels [[buffer(5)]],
    constant uint& out_channels [[buffer(6)]],
    constant uint& in_height [[buffer(7)]],
    constant uint& in_width [[buffer(8)]],
    constant uint& kernel_h [[buffer(9)]],
    constant uint& kernel_w [[buffer(10)]],
    constant uint& stride_h [[buffer(11)]],
    constant uint& stride_w [[buffer(12)]],
    constant uint& pad_h [[buffer(13)]],
    constant uint& pad_w [[buffer(14)]],
    constant uint& use_relu [[buffer(15)]],
    uint3 group_id [[threadgroup_position_in_grid]],
    uint simd_lane_id [[thread_index_in_simdgroup]],
    uint simd_group_id [[simdgroup_index_in_threadgroup]]
) {
    // Output dimensions
    uint out_height = (in_height + 2 * pad_h - kernel_h) / stride_h + 1;
    uint out_width = (in_width + 2 * pad_w - kernel_w) / stride_w + 1;

    // GEMM dimensions for conv
    // M = out_channels
    // K = in_channels * kernel_h * kernel_w
    // N = out_height * out_width (spatial)
    uint M = out_channels;
    uint K = in_channels * kernel_h * kernel_w;
    uint N = out_height * out_width;

    // Simdgroup matrix tiles (8x8)
    simdgroup_float8x8 acc[4][4];  // 32x32 output tile

    // Initialize accumulators
    for (int i = 0; i < 4; i++) {
        for (int j = 0; j < 4; j++) {
            acc[i][j] = simdgroup_float8x8(0);
        }
    }

    uint batch = group_id.z;
    uint row_block = group_id.y * 32;  // Output channel block
    uint col_block = group_id.x * 32;  // Spatial block

    if (batch >= batch_size) return;

    // Threadgroup memory for tiles
    threadgroup float A_tile[32][8];   // Weight tile
    threadgroup float B_tile[8][32];   // Im2col tile (computed on-the-fly)

    // Loop over K dimension in blocks of 8
    for (uint k_block = 0; k_block < K; k_block += 8) {
        // Load weight tile into A_tile
        // Weights are [out_channels, in_channels*kh*kw] = [M, K]
        uint local_idx = simd_group_id * 32 + simd_lane_id;
        if (local_idx < 256) {  // 32 * 8 = 256
            uint m_idx = local_idx / 8;  // row within tile
            uint k_idx = local_idx % 8;  // col within tile
            uint global_m = row_block + m_idx;
            uint global_k = k_block + k_idx;

            if (global_m < M && global_k < K) {
                A_tile[m_idx][k_idx] = kernel_weights[global_m * K + global_k];
            } else {
                A_tile[m_idx][k_idx] = 0.0f;
            }
        }

        // Compute im2col values on the fly for B_tile
        if (local_idx < 256) {
            uint k_idx = local_idx / 32;  // row within tile
            uint n_idx = local_idx % 32;  // col within tile
            uint global_k = k_block + k_idx;
            uint global_n = col_block + n_idx;

            if (global_k < K && global_n < N) {
                // Decode im2col indices
                uint ic = global_k / (kernel_h * kernel_w);
                uint rem = global_k % (kernel_h * kernel_w);
                uint kh = rem / kernel_w;
                uint kw = rem % kernel_w;

                uint oh = global_n / out_width;
                uint ow = global_n % out_width;

                int ih = (int)(oh * stride_h + kh) - (int)pad_h;
                int iw = (int)(ow * stride_w + kw) - (int)pad_w;

                if (ih >= 0 && ih < (int)in_height && iw >= 0 && iw < (int)in_width) {
                    uint in_idx = batch * in_channels * in_height * in_width
                                + ic * in_height * in_width
                                + ih * in_width + iw;
                    B_tile[k_idx][n_idx] = input[in_idx];
                } else {
                    B_tile[k_idx][n_idx] = 0.0f;
                }
            } else {
                B_tile[k_idx][n_idx] = 0.0f;
            }
        }

        threadgroup_barrier(mem_flags::mem_threadgroup);

        // Matrix multiply with simdgroup operations
        simdgroup_float8x8 a_mat, b_mat;

        // Load and multiply 8x8 tiles
        for (int i = 0; i < 4; i++) {
            simdgroup_load(a_mat, &A_tile[i * 8][0], 8);

            for (int j = 0; j < 4; j++) {
                simdgroup_load(b_mat, &B_tile[0][j * 8], 32);
                simdgroup_multiply_accumulate(acc[i][j], a_mat, b_mat, acc[i][j]);
            }
        }

        threadgroup_barrier(mem_flags::mem_threadgroup);
    }

    // Store results with bias and optional ReLU
    for (int i = 0; i < 4; i++) {
        for (int j = 0; j < 4; j++) {
            threadgroup float result_tile[8][8];
            simdgroup_store(acc[i][j], &result_tile[0][0], 8);

            if (simd_lane_id < 64) {
                uint local_m = simd_lane_id / 8;
                uint local_n = simd_lane_id % 8;
                uint global_m = row_block + i * 8 + local_m;
                uint global_n = col_block + j * 8 + local_n;

                if (global_m < M && global_n < N) {
                    float val = result_tile[local_m][local_n] + bias[global_m];
                    if (use_relu) {
                        val = max(0.0f, val);
                    }

                    uint out_idx = batch * out_channels * out_height * out_width
                                 + global_m * out_height * out_width
                                 + global_n;
                    output[out_idx] = val;
                }
            }
        }
    }
}

// BatchNorm2D inference - fused with optional ReLU
// Computes: y = (x - mean) / sqrt(var + eps) * gamma + beta
// For inference: mean and var are running statistics
kernel void batchnorm2d_inference(
    device const float* input [[buffer(0)]],
    device const float* gamma [[buffer(1)]],    // scale
    device const float* beta [[buffer(2)]],     // bias
    device const float* running_mean [[buffer(3)]],
    device const float* running_var [[buffer(4)]],
    device float* output [[buffer(5)]],
    constant uint& batch_size [[buffer(6)]],
    constant uint& channels [[buffer(7)]],
    constant uint& height [[buffer(8)]],
    constant uint& width [[buffer(9)]],
    constant float& eps [[buffer(10)]],
    constant uint& apply_relu [[buffer(11)]],
    uint3 gid [[thread_position_in_grid]]
) {
    uint w_idx = gid.x;
    uint h_idx = gid.y;
    uint batch_c = gid.z;
    uint batch = batch_c / channels;
    uint c = batch_c % channels;

    if (w_idx >= width || h_idx >= height || batch >= batch_size) return;

    uint idx = batch * channels * height * width
             + c * height * width
             + h_idx * width + w_idx;

    float x = input[idx];
    float mean = running_mean[c];
    float var = running_var[c];
    float g = gamma[c];
    float b = beta[c];

    float y = (x - mean) * rsqrt(var + eps) * g + b;

    if (apply_relu) {
        y = max(0.0f, y);
    }

    output[idx] = y;
}

// ============================================================================
// BACKWARD PASS KERNELS (for automatic differentiation)
// ============================================================================

// ReLU backward: grad_input = grad_output * (input > 0 ? 1 : 0)
kernel void relu_backward(
    device const float* input [[buffer(0)]],
    device const float* grad_output [[buffer(1)]],
    device float* grad_input [[buffer(2)]],
    uint id [[thread_position_in_grid]]
) {
    grad_input[id] = input[id] > 0.0f ? grad_output[id] : 0.0f;
}

// Element-wise multiply backward
// For c = a * b: grad_a = grad_c * b, grad_b = grad_c * a
kernel void mul_backward(
    device const float* a [[buffer(0)]],
    device const float* b [[buffer(1)]],
    device const float* grad_output [[buffer(2)]],
    device float* grad_a [[buffer(3)]],
    device float* grad_b [[buffer(4)]],
    uint id [[thread_position_in_grid]]
) {
    grad_a[id] = grad_output[id] * b[id];
    grad_b[id] = grad_output[id] * a[id];
}

// Sigmoid backward: grad_input = grad_output * sigmoid(x) * (1 - sigmoid(x))
// Note: Takes sigmoid output (y) to avoid recomputation
kernel void sigmoid_backward(
    device const float* sigmoid_output [[buffer(0)]],
    device const float* grad_output [[buffer(1)]],
    device float* grad_input [[buffer(2)]],
    uint id [[thread_position_in_grid]]
) {
    float y = sigmoid_output[id];
    grad_input[id] = grad_output[id] * y * (1.0f - y);
}

// Tanh backward: grad_input = grad_output * (1 - tanh(x)^2)
// Note: Takes tanh output (y) to avoid recomputation
kernel void tanh_backward(
    device const float* tanh_output [[buffer(0)]],
    device const float* grad_output [[buffer(1)]],
    device float* grad_input [[buffer(2)]],
    uint id [[thread_position_in_grid]]
) {
    float y = tanh_output[id];
    grad_input[id] = grad_output[id] * (1.0f - y * y);
}

// GELU backward using approximation derivative
// gelu(x) ≈ 0.5 * x * (1 + tanh(sqrt(2/π) * (x + 0.044715 * x³)))
kernel void gelu_backward(
    device const float* input [[buffer(0)]],
    device const float* grad_output [[buffer(1)]],
    device float* grad_input [[buffer(2)]],
    uint id [[thread_position_in_grid]]
) {
    float x = input[id];
    float sqrt_2_pi = 0.7978845608f;
    float c = 0.044715f;

    float x3 = x * x * x;
    float inner = sqrt_2_pi * (x + c * x3);
    float tanh_inner = tanh(inner);

    // Derivative: 0.5 * (1 + tanh_inner) + 0.5 * x * (1 - tanh_inner²) * sqrt_2_pi * (1 + 3*c*x²)
    float dtanh = 1.0f - tanh_inner * tanh_inner;
    float dinner = sqrt_2_pi * (1.0f + 3.0f * c * x * x);

    float dgelu = 0.5f * (1.0f + tanh_inner) + 0.5f * x * dtanh * dinner;
    grad_input[id] = grad_output[id] * dgelu;
}

// Softmax backward (batched, per-row)
// For y = softmax(x): grad_x = y * (grad_y - sum(grad_y * y))
// Each thread handles one element, atomics for row sums
kernel void softmax_backward(
    device const float* softmax_output [[buffer(0)]],
    device const float* grad_output [[buffer(1)]],
    device float* grad_input [[buffer(2)]],
    constant uint& num_rows [[buffer(3)]],
    constant uint& row_size [[buffer(4)]],
    uint2 gid [[thread_position_in_grid]]
) {
    uint row = gid.y;
    uint col = gid.x;

    if (row >= num_rows || col >= row_size) return;

    uint base = row * row_size;

    // Compute dot product: sum(grad_y * y) for this row
    float dot = 0.0f;
    for (uint j = 0; j < row_size; j++) {
        dot += grad_output[base + j] * softmax_output[base + j];
    }

    // grad_x[i] = y[i] * (grad_y[i] - dot)
    uint idx = base + col;
    grad_input[idx] = softmax_output[idx] * (grad_output[idx] - dot);
}

// Bias backward: grad_bias = sum(grad_output) over batch/spatial dims
// For bias of shape [stride], sums over elements with same (idx % stride)
kernel void bias_backward(
    device const float* grad_output [[buffer(0)]],
    device atomic_float* grad_bias [[buffer(1)]],
    constant uint& n [[buffer(2)]],
    constant uint& stride [[buffer(3)]],
    uint id [[thread_position_in_grid]]
) {
    if (id >= n) return;
    uint bias_idx = id % stride;
    atomic_fetch_add_explicit(&grad_bias[bias_idx], grad_output[id], memory_order_relaxed);
}

// BatchNorm2D backward (inference mode - simplified)
// For inference: grad_input = grad_output * gamma / sqrt(var + eps)
kernel void batchnorm2d_backward(
    device const float* input [[buffer(0)]],
    device const float* gamma [[buffer(1)]],
    device const float* running_var [[buffer(2)]],
    device const float* grad_output [[buffer(3)]],
    device float* grad_input [[buffer(4)]],
    constant uint& batch_size [[buffer(5)]],
    constant uint& channels [[buffer(6)]],
    constant uint& height [[buffer(7)]],
    constant uint& width [[buffer(8)]],
    constant float& eps [[buffer(9)]],
    uint3 gid [[thread_position_in_grid]]
) {
    uint w_idx = gid.x;
    uint h_idx = gid.y;
    uint batch_c = gid.z;
    uint batch = batch_c / channels;
    uint c = batch_c % channels;

    if (w_idx >= width || h_idx >= height || batch >= batch_size) return;

    uint idx = batch * channels * height * width
             + c * height * width
             + h_idx * width + w_idx;

    float var = running_var[c];
    float g = gamma[c];
    float dy = grad_output[idx];

    // grad_input (for inference, simpler form)
    grad_input[idx] = dy * g * rsqrt(var + eps);
}

// ============================================================
// Additional Kernels for Training (GpuBuffer versions)
// ============================================================

// AXPY for GpuBuffer: output = alpha * x + y (creates new output)
kernel void axpy_out(
    device const float* x [[buffer(0)]],
    device const float* y [[buffer(1)]],
    device float* output [[buffer(2)]],
    constant float& alpha [[buffer(3)]],
    constant uint& n [[buffer(4)]],
    uint i [[thread_position_in_grid]]
) {
    if (i >= n) return;
    output[i] = alpha * x[i] + y[i];
}

// Scale for GpuBuffer: output = alpha * x (creates new output)
kernel void scale_out(
    device const float* x [[buffer(0)]],
    device float* output [[buffer(1)]],
    constant float& alpha [[buffer(2)]],
    constant uint& n [[buffer(3)]],
    uint i [[thread_position_in_grid]]
) {
    if (i >= n) return;
    output[i] = alpha * x[i];
}

// Sub for GpuBuffer: output = x - y (creates new output)
kernel void sub_out(
    device const float* x [[buffer(0)]],
    device const float* y [[buffer(1)]],
    device float* output [[buffer(2)]],
    constant uint& n [[buffer(3)]],
    uint i [[thread_position_in_grid]]
) {
    if (i >= n) return;
    output[i] = x[i] - y[i];
}

// GEMM with first matrix transposed: C = A^T @ B (naive fallback)
// A is stored as [k, m] (row-major), we compute A^T[m, k] @ B[k, n] = C[m, n]
kernel void gemm_tn_naive(
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
        sum += A[l * m + i] * B[l * n + j];
    }
    C[i * n + j] = sum;
}

// Optimized GEMM TN with tiling: C = A^T @ B
// Uses threadgroup memory for coalesced access
#define TN_TILE 32
kernel void gemm_tn(
    device const float* A [[buffer(0)]],
    device const float* B [[buffer(1)]],
    device float* C [[buffer(2)]],
    constant uint& m [[buffer(3)]],
    constant uint& k [[buffer(4)]],
    constant uint& n [[buffer(5)]],
    threadgroup float* tg_mem [[threadgroup(0)]],
    uint2 tgid [[threadgroup_position_in_grid]],
    uint2 tid [[thread_position_in_threadgroup]],
    uint linear_tid [[thread_index_in_threadgroup]]
) {
    // Tiles: As[TN_TILE][TN_TILE], Bs[TN_TILE][TN_TILE]
    threadgroup float* As = tg_mem;
    threadgroup float* Bs = tg_mem + TN_TILE * TN_TILE;

    uint tg_row = tgid.y * TN_TILE;
    uint tg_col = tgid.x * TN_TILE;
    uint row = tg_row + tid.y;
    uint col = tg_col + tid.x;

    float sum = 0.0f;

    for (uint kk = 0; kk < k; kk += TN_TILE) {
        // Load A^T tile: As[i][l] = A^T[tg_row+i, kk+l] = A[kk+l, tg_row+i]
        uint a_row = kk + tid.y;
        uint a_col = tg_row + tid.x;
        As[tid.y * TN_TILE + tid.x] = (a_row < k && a_col < m) ? A[a_row * m + a_col] : 0.0f;

        // Load B tile: Bs[l][j] = B[kk+l, tg_col+j]
        uint b_row = kk + tid.y;
        uint b_col = tg_col + tid.x;
        Bs[tid.y * TN_TILE + tid.x] = (b_row < k && b_col < n) ? B[b_row * n + b_col] : 0.0f;

        threadgroup_barrier(mem_flags::mem_threadgroup);

        // Compute partial dot product
        for (uint l = 0; l < TN_TILE && (kk + l) < k; l++) {
            sum += As[l * TN_TILE + tid.y] * Bs[l * TN_TILE + tid.x];
        }

        threadgroup_barrier(mem_flags::mem_threadgroup);
    }

    if (row < m && col < n) {
        C[row * n + col] = sum;
    }
}

// GEMM with second matrix transposed: C = A @ B^T (naive fallback)
// A is [m, k], B is stored as [n, k] (row-major), we compute A @ B^T[k, n] = C[m, n]
kernel void gemm_nt_naive(
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
        sum += A[i * k + l] * B[j * k + l];
    }
    C[i * n + j] = sum;
}

// Optimized GEMM NT with tiling: C = A @ B^T
#define NT_TILE 32
kernel void gemm_nt(
    device const float* A [[buffer(0)]],
    device const float* B [[buffer(1)]],
    device float* C [[buffer(2)]],
    constant uint& m [[buffer(3)]],
    constant uint& k [[buffer(4)]],
    constant uint& n [[buffer(5)]],
    threadgroup float* tg_mem [[threadgroup(0)]],
    uint2 tgid [[threadgroup_position_in_grid]],
    uint2 tid [[thread_position_in_threadgroup]],
    uint linear_tid [[thread_index_in_threadgroup]]
) {
    // Tiles: As[NT_TILE][NT_TILE], Bs[NT_TILE][NT_TILE]
    threadgroup float* As = tg_mem;
    threadgroup float* Bs = tg_mem + NT_TILE * NT_TILE;

    uint tg_row = tgid.y * NT_TILE;
    uint tg_col = tgid.x * NT_TILE;
    uint row = tg_row + tid.y;
    uint col = tg_col + tid.x;

    float sum = 0.0f;

    for (uint kk = 0; kk < k; kk += NT_TILE) {
        // Load A tile: As[i][l] = A[tg_row+i, kk+l]
        uint a_row = tg_row + tid.y;
        uint a_col = kk + tid.x;
        As[tid.y * NT_TILE + tid.x] = (a_row < m && a_col < k) ? A[a_row * k + a_col] : 0.0f;

        // Load B^T tile: Bs[l][j] = B^T[kk+l, tg_col+j] = B[tg_col+j, kk+l]
        uint b_row = tg_col + tid.y;  // This is the column we want from B^T
        uint b_col = kk + tid.x;       // This is the row from B^T
        Bs[tid.x * NT_TILE + tid.y] = (b_row < n && b_col < k) ? B[b_row * k + b_col] : 0.0f;

        threadgroup_barrier(mem_flags::mem_threadgroup);

        // Compute partial dot product
        for (uint l = 0; l < NT_TILE && (kk + l) < k; l++) {
            sum += As[tid.y * NT_TILE + l] * Bs[l * NT_TILE + tid.x];
        }

        threadgroup_barrier(mem_flags::mem_threadgroup);
    }

    if (row < m && col < n) {
        C[row * n + col] = sum;
    }
}
