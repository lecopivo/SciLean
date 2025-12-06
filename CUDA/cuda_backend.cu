// CUDA Backend for SciLean
// Mirrors Metal/metal_backend.mm structure
//
// Build: nvcc -shared -o libscileancuda.so cuda_backend.cu -lcuda -lcublas
// Or compile to object: nvcc -c -o cuda_backend.o cuda_backend.cu

#include <cuda_runtime.h>
#include <cublas_v2.h>
#include <lean/lean.h>
#include <stdio.h>
#include <stdlib.h>

// Global cuBLAS handle (lazy init)
static cublasHandle_t g_cublas_handle = nullptr;
static bool g_cuda_initialized = false;

// Initialize CUDA and cuBLAS
static bool ensure_cuda_init() {
    if (g_cuda_initialized) return true;

    int device_count = 0;
    cudaError_t err = cudaGetDeviceCount(&device_count);
    if (err != cudaSuccess || device_count == 0) {
        fprintf(stderr, "CUDA: No devices found\n");
        return false;
    }

    err = cudaSetDevice(0);
    if (err != cudaSuccess) {
        fprintf(stderr, "CUDA: Failed to set device\n");
        return false;
    }

    cublasStatus_t status = cublasCreate(&g_cublas_handle);
    if (status != CUBLAS_STATUS_SUCCESS) {
        fprintf(stderr, "cuBLAS: Failed to create handle\n");
        return false;
    }

    g_cuda_initialized = true;
    return true;
}

// Check if CUDA is available
extern "C" LEAN_EXPORT uint8_t scilean_cuda_available(lean_object* /* unused */) {
    return ensure_cuda_init() ? 1 : 0;
}

// Get device name
extern "C" LEAN_EXPORT lean_obj_res scilean_cuda_device_name(lean_object* /* unused */) {
    if (!ensure_cuda_init()) {
        return lean_mk_string("No CUDA device");
    }

    cudaDeviceProp prop;
    cudaGetDeviceProperties(&prop, 0);
    return lean_mk_string(prop.name);
}

//==============================================================================
// GEMM Kernels
//==============================================================================

// Naive GEMM kernel (for comparison)
__global__ void gemm_naive_kernel(
    const float* __restrict__ A,
    const float* __restrict__ B,
    float* __restrict__ C,
    int M, int K, int N
) {
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;

    if (row < M && col < N) {
        float sum = 0.0f;
        for (int k = 0; k < K; k++) {
            sum += A[row * K + k] * B[k * N + col];
        }
        C[row * N + col] = sum;
    }
}

// Tiled GEMM kernel with shared memory
#define TILE_SIZE 32

__global__ void gemm_tiled_kernel(
    const float* __restrict__ A,
    const float* __restrict__ B,
    float* __restrict__ C,
    int M, int K, int N
) {
    __shared__ float As[TILE_SIZE][TILE_SIZE];
    __shared__ float Bs[TILE_SIZE][TILE_SIZE];

    int row = blockIdx.y * TILE_SIZE + threadIdx.y;
    int col = blockIdx.x * TILE_SIZE + threadIdx.x;
    float sum = 0.0f;

    for (int t = 0; t < (K + TILE_SIZE - 1) / TILE_SIZE; t++) {
        int aCol = t * TILE_SIZE + threadIdx.x;
        int bRow = t * TILE_SIZE + threadIdx.y;

        As[threadIdx.y][threadIdx.x] = (row < M && aCol < K) ? A[row * K + aCol] : 0.0f;
        Bs[threadIdx.y][threadIdx.x] = (bRow < K && col < N) ? B[bRow * N + col] : 0.0f;

        __syncthreads();

        #pragma unroll
        for (int i = 0; i < TILE_SIZE; i++) {
            sum += As[threadIdx.y][i] * Bs[i][threadIdx.x];
        }

        __syncthreads();
    }

    if (row < M && col < N) {
        C[row * N + col] = sum;
    }
}

// Helper: ByteArray to device pointer
static float* bytearray_to_device(lean_object* arr, size_t* out_size) {
    size_t size = lean_sarray_size(arr);
    *out_size = size;

    uint8_t* host_data = lean_sarray_cptr(arr);
    float* device_ptr;

    cudaMalloc(&device_ptr, size);
    cudaMemcpy(device_ptr, host_data, size, cudaMemcpyHostToDevice);

    return device_ptr;
}

// Helper: device pointer to new ByteArray
static lean_object* device_to_bytearray(float* device_ptr, size_t size) {
    lean_object* result = lean_alloc_sarray(1, size, size);
    uint8_t* host_data = lean_sarray_cptr(result);

    cudaMemcpy(host_data, device_ptr, size, cudaMemcpyDeviceToHost);
    cudaFree(device_ptr);

    return result;
}

//==============================================================================
// Lean FFI Functions
//==============================================================================

// GEMM using tiled kernel
extern "C" LEAN_EXPORT lean_obj_res scilean_cuda_gemm_tiled(
    size_t m, size_t k, size_t n,
    b_lean_obj_arg A_arr, b_lean_obj_arg B_arr
) {
    if (!ensure_cuda_init()) {
        // Return empty array on failure
        return lean_alloc_sarray(1, 0, 0);
    }

    size_t a_size, b_size;
    float* d_A = bytearray_to_device(A_arr, &a_size);
    float* d_B = bytearray_to_device(B_arr, &b_size);

    size_t c_size = m * n * sizeof(float);
    float* d_C;
    cudaMalloc(&d_C, c_size);

    dim3 block(TILE_SIZE, TILE_SIZE);
    dim3 grid((n + TILE_SIZE - 1) / TILE_SIZE, (m + TILE_SIZE - 1) / TILE_SIZE);

    gemm_tiled_kernel<<<grid, block>>>(d_A, d_B, d_C, m, k, n);
    cudaDeviceSynchronize();

    cudaFree(d_A);
    cudaFree(d_B);

    return device_to_bytearray(d_C, c_size);
}

// GEMM using cuBLAS (optimized)
extern "C" LEAN_EXPORT lean_obj_res scilean_cuda_gemm_cublas(
    size_t m, size_t k, size_t n,
    b_lean_obj_arg A_arr, b_lean_obj_arg B_arr
) {
    if (!ensure_cuda_init()) {
        return lean_alloc_sarray(1, 0, 0);
    }

    size_t a_size, b_size;
    float* d_A = bytearray_to_device(A_arr, &a_size);
    float* d_B = bytearray_to_device(B_arr, &b_size);

    size_t c_size = m * n * sizeof(float);
    float* d_C;
    cudaMalloc(&d_C, c_size);

    // cuBLAS uses column-major, so we compute C = B^T * A^T to get row-major C
    // Or equivalently: C_row = (A_row * B_row) via cublasSgemm with transposed args
    const float alpha = 1.0f;
    const float beta = 0.0f;

    // cublasSgemm: C = alpha * A * B + beta * C
    // For row-major: we do C^T = B^T * A^T, then read C as row-major
    cublasSgemm(g_cublas_handle,
                CUBLAS_OP_N, CUBLAS_OP_N,
                n, m, k,
                &alpha,
                d_B, n,   // B is K×N, leading dim = N
                d_A, k,   // A is M×K, leading dim = K
                &beta,
                d_C, n);  // C is M×N, leading dim = N

    cudaDeviceSynchronize();

    cudaFree(d_A);
    cudaFree(d_B);

    return device_to_bytearray(d_C, c_size);
}

// Naive GEMM (for benchmarking)
extern "C" LEAN_EXPORT lean_obj_res scilean_cuda_gemm_naive(
    size_t m, size_t k, size_t n,
    b_lean_obj_arg A_arr, b_lean_obj_arg B_arr
) {
    if (!ensure_cuda_init()) {
        return lean_alloc_sarray(1, 0, 0);
    }

    size_t a_size, b_size;
    float* d_A = bytearray_to_device(A_arr, &a_size);
    float* d_B = bytearray_to_device(B_arr, &b_size);

    size_t c_size = m * n * sizeof(float);
    float* d_C;
    cudaMalloc(&d_C, c_size);

    dim3 block(16, 16);
    dim3 grid((n + 15) / 16, (m + 15) / 16);

    gemm_naive_kernel<<<grid, block>>>(d_A, d_B, d_C, m, k, n);
    cudaDeviceSynchronize();

    cudaFree(d_A);
    cudaFree(d_B);

    return device_to_bytearray(d_C, c_size);
}

//==============================================================================
// Element-wise operations
//==============================================================================

__global__ void add_kernel(const float* a, const float* b, float* c, int n) {
    int i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i < n) c[i] = a[i] + b[i];
}

__global__ void mul_kernel(const float* a, const float* b, float* c, int n) {
    int i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i < n) c[i] = a[i] * b[i];
}

__global__ void axpy_kernel(float a, const float* x, float* y, int n) {
    int i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i < n) y[i] = a * x[i] + y[i];
}

extern "C" LEAN_EXPORT lean_obj_res scilean_cuda_add(
    size_t n,
    b_lean_obj_arg A_arr, b_lean_obj_arg B_arr
) {
    if (!ensure_cuda_init()) {
        return lean_alloc_sarray(1, 0, 0);
    }

    size_t a_size, b_size;
    float* d_A = bytearray_to_device(A_arr, &a_size);
    float* d_B = bytearray_to_device(B_arr, &b_size);

    size_t c_size = n * sizeof(float);
    float* d_C;
    cudaMalloc(&d_C, c_size);

    int block = 256;
    int grid = (n + block - 1) / block;

    add_kernel<<<grid, block>>>(d_A, d_B, d_C, n);
    cudaDeviceSynchronize();

    cudaFree(d_A);
    cudaFree(d_B);

    return device_to_bytearray(d_C, c_size);
}

//==============================================================================
// Reduction operations
//==============================================================================

__global__ void reduce_sum_kernel(const float* input, float* output, int n) {
    extern __shared__ float sdata[];

    int tid = threadIdx.x;
    int i = blockIdx.x * blockDim.x * 2 + threadIdx.x;

    float sum = 0.0f;
    if (i < n) sum = input[i];
    if (i + blockDim.x < n) sum += input[i + blockDim.x];
    sdata[tid] = sum;

    __syncthreads();

    for (int s = blockDim.x / 2; s > 0; s >>= 1) {
        if (tid < s) {
            sdata[tid] += sdata[tid + s];
        }
        __syncthreads();
    }

    if (tid == 0) output[blockIdx.x] = sdata[0];
}

extern "C" LEAN_EXPORT float scilean_cuda_reduce_sum(
    size_t n,
    b_lean_obj_arg arr
) {
    if (!ensure_cuda_init()) {
        return 0.0f;
    }

    size_t size;
    float* d_input = bytearray_to_device(arr, &size);

    int block = 256;
    int grid = (n + block * 2 - 1) / (block * 2);

    float* d_output;
    cudaMalloc(&d_output, grid * sizeof(float));

    reduce_sum_kernel<<<grid, block, block * sizeof(float)>>>(d_input, d_output, n);

    // Second pass if needed
    while (grid > 1) {
        int new_grid = (grid + block * 2 - 1) / (block * 2);
        float* d_temp;
        cudaMalloc(&d_temp, new_grid * sizeof(float));
        reduce_sum_kernel<<<new_grid, block, block * sizeof(float)>>>(d_output, d_temp, grid);
        cudaFree(d_output);
        d_output = d_temp;
        grid = new_grid;
    }

    float result;
    cudaMemcpy(&result, d_output, sizeof(float), cudaMemcpyDeviceToHost);

    cudaFree(d_input);
    cudaFree(d_output);

    return result;
}
