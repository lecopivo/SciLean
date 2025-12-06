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
// REQUIRES: M, N, K are multiples of 128
// Uses Metal 3 features available on M4

#define M4_TILE_M 128
#define M4_TILE_N 128
#define M4_TILE_K 32

kernel void gemm_m4(
    device const float4* A [[buffer(0)]],  // Treat as float4 for vectorized loads
    device const float4* B [[buffer(1)]],
    device float* C [[buffer(2)]],
    constant uint& M [[buffer(3)]],
    constant uint& K [[buffer(4)]],
    constant uint& N [[buffer(5)]],
    uint2 tgid [[threadgroup_position_in_grid]],
    uint2 tid [[thread_position_in_threadgroup]],
    uint simd_id [[simdgroup_index_in_threadgroup]]
) {
    // Shared memory: 128×32 for A, 32×128 for B
    threadgroup float As[M4_TILE_M][M4_TILE_K + 1];  // +1 to avoid bank conflicts
    threadgroup float Bs[M4_TILE_K][M4_TILE_N + 1];

    // Each threadgroup: 128×128 output, 512 threads = 16 simdgroups
    // Each simdgroup: 32×32 output (4×4 grid of 8×8)
    uint tg_row = tgid.y * M4_TILE_M;
    uint tg_col = tgid.x * M4_TILE_N;

    // Simdgroup layout: 4×4 grid
    uint simd_row = tg_row + (simd_id / 4) * 32;
    uint simd_col = tg_col + (simd_id % 4) * 32;

    // 4×4 grid of 8×8 accumulators = 32×32 per simdgroup
    simdgroup_float8x8 acc[4][4];
    #pragma unroll
    for (int i = 0; i < 4; i++) {
        #pragma unroll
        for (int j = 0; j < 4; j++) {
            acc[i][j] = simdgroup_float8x8(0);
        }
    }

    // Thread ID for loading (512 threads)
    uint linear_tid = tid.y * 32 + tid.x;
    uint K4 = K / 4;  // K in float4 units
    uint N4 = N / 4;

    // Main loop over K
    for (uint k = 0; k < K; k += M4_TILE_K) {
        // Load A tile: 128×32 = 4096 floats, 512 threads → 8 floats each
        // Using float4 loads: 2 float4 per thread
        #pragma unroll
        for (uint i = 0; i < 2; i++) {
            uint idx = linear_tid * 2 + i;
            uint ar = idx / 8;   // row in tile (0-127)
            uint ac4 = idx % 8;  // col in float4 units
            uint global_row = tg_row + ar;
            uint global_k4 = (k / 4) + ac4;

            float4 val = A[global_row * K4 + global_k4];
            As[ar][ac4 * 4 + 0] = val.x;
            As[ar][ac4 * 4 + 1] = val.y;
            As[ar][ac4 * 4 + 2] = val.z;
            As[ar][ac4 * 4 + 3] = val.w;
        }

        // Load B tile: 32×128 = 4096 floats
        #pragma unroll
        for (uint i = 0; i < 2; i++) {
            uint idx = linear_tid * 2 + i;
            uint br = idx / 32;  // row in tile (0-31)
            uint bc4 = idx % 32; // col in float4 units
            uint global_k = k + br;
            uint global_c4 = (tg_col / 4) + bc4;

            float4 val = B[global_k * N4 + global_c4];
            Bs[br][bc4 * 4 + 0] = val.x;
            Bs[br][bc4 * 4 + 1] = val.y;
            Bs[br][bc4 * 4 + 2] = val.z;
            Bs[br][bc4 * 4 + 3] = val.w;
        }

        threadgroup_barrier(mem_flags::mem_threadgroup);

        // Compute: 32 in K tile, 8 at a time
        uint simd_row_local = (simd_id / 4) * 32;
        uint simd_col_local = (simd_id % 4) * 32;

        #pragma unroll
        for (uint kk = 0; kk < M4_TILE_K; kk += 8) {
            simdgroup_float8x8 a[4], b[4];

            // Load 4 A blocks (32×8 region)
            #pragma unroll
            for (int ai = 0; ai < 4; ai++) {
                simdgroup_load(a[ai], &As[simd_row_local + ai * 8][kk], M4_TILE_K + 1);
            }

            // Load 4 B blocks (8×32 region)
            #pragma unroll
            for (int bi = 0; bi < 4; bi++) {
                simdgroup_load(b[bi], &Bs[kk][simd_col_local + bi * 8], M4_TILE_N + 1);
            }

            // Full 4×4 multiply-accumulate
            #pragma unroll
            for (int ai = 0; ai < 4; ai++) {
                #pragma unroll
                for (int bi = 0; bi < 4; bi++) {
                    simdgroup_multiply_accumulate(acc[ai][bi], a[ai], b[bi], acc[ai][bi]);
                }
            }
        }

        threadgroup_barrier(mem_flags::mem_threadgroup);
    }

    // Store 32×32 output (no bounds check - assume aligned)
    #pragma unroll
    for (int ai = 0; ai < 4; ai++) {
        #pragma unroll
        for (int bi = 0; bi < 4; bi++) {
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
