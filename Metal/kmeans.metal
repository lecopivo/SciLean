#include <metal_stdlib>
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

// Matrix multiply: C = A * B
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

// Reduction sum (single workgroup version - simple)
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
