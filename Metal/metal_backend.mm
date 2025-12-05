#import <Metal/Metal.h>
#import <Foundation/Foundation.h>
#import <MetalPerformanceShaders/MetalPerformanceShaders.h>
#import <Accelerate/Accelerate.h>
#include <lean/lean.h>

// Global Metal state
static id<MTLDevice> device = nil;
static id<MTLCommandQueue> commandQueue = nil;
static id<MTLLibrary> library = nil;
static NSMutableDictionary<NSString*, id<MTLComputePipelineState>>* pipelines = nil;

// Initialize Metal
static bool ensure_metal_initialized() {
    if (device != nil) return true;

    @autoreleasepool {
        device = MTLCreateSystemDefaultDevice();
        if (!device) {
            NSLog(@"Metal is not supported on this device");
            return false;
        }

        commandQueue = [device newCommandQueue];

        // Load the default library (compiled .metallib)
        NSError* error = nil;
        NSString* libraryPath = [[NSBundle mainBundle] pathForResource:@"default" ofType:@"metallib"];
        if (libraryPath) {
            NSURL* libraryURL = [NSURL fileURLWithPath:libraryPath];
            library = [device newLibraryWithURL:libraryURL error:&error];
        }

        // Try loading from source if metallib not found
        if (!library) {
            NSString* sourcePath = @"Metal/kmeans.metal";
            NSString* source = [NSString stringWithContentsOfFile:sourcePath
                                                         encoding:NSUTF8StringEncoding
                                                            error:&error];
            if (source) {
                MTLCompileOptions* options = [[MTLCompileOptions alloc] init];
                library = [device newLibraryWithSource:source options:options error:&error];
            }
        }

        if (!library) {
            NSLog(@"Failed to load Metal library: %@", error);
            return false;
        }

        pipelines = [NSMutableDictionary dictionary];
    }
    return true;
}

// Get or create a compute pipeline for a kernel
static id<MTLComputePipelineState> get_pipeline(NSString* kernelName) {
    id<MTLComputePipelineState> pipeline = pipelines[kernelName];
    if (pipeline) return pipeline;

    @autoreleasepool {
        NSError* error = nil;
        id<MTLFunction> function = [library newFunctionWithName:kernelName];
        if (!function) {
            NSLog(@"Failed to find kernel: %@", kernelName);
            return nil;
        }

        pipeline = [device newComputePipelineStateWithFunction:function error:&error];
        if (!pipeline) {
            NSLog(@"Failed to create pipeline for %@: %@", kernelName, error);
            return nil;
        }

        pipelines[kernelName] = pipeline;
    }
    return pipeline;
}

// Create a Metal buffer from a Lean FloatArray (Lean uses double, Metal uses float)
static id<MTLBuffer> create_buffer_from_float_array(b_lean_obj_arg arr, bool readonly) {
    size_t count = lean_sarray_size(arr);
    double* lean_data = (double*)lean_sarray_cptr(arr);

    MTLResourceOptions options = readonly ?
        MTLResourceStorageModeShared | MTLResourceCPUCacheModeDefaultCache :
        MTLResourceStorageModeShared;

    // Convert double to float for Metal
    id<MTLBuffer> buffer = [device newBufferWithLength:count * sizeof(float) options:options];
    float* metal_data = (float*)[buffer contents];
    for (size_t i = 0; i < count; i++) {
        metal_data[i] = (float)lean_data[i];
    }
    return buffer;
}

// Copy Metal buffer back to Lean FloatArray (convert float back to double)
static lean_obj_res buffer_to_float_array(id<MTLBuffer> buffer, size_t count) {
    lean_obj_res arr = lean_alloc_sarray(sizeof(double), count, count);
    float* metal_data = (float*)[buffer contents];
    double* lean_data = (double*)lean_sarray_cptr(arr);
    for (size_t i = 0; i < count; i++) {
        lean_data[i] = (double)metal_data[i];
    }
    return arr;
}

extern "C" {

// KMeans loss on GPU
LEAN_EXPORT double scilean_metal_kmeans(
    size_t d, size_t n, size_t k,
    b_lean_obj_arg points,
    b_lean_obj_arg centroids
) {
    if (!ensure_metal_initialized()) {
        // Fallback to CPU
        return -1.0;
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"kmeans_loss");
        if (!pipeline) return -1.0;

        // Create buffers
        id<MTLBuffer> pointsBuf = create_buffer_from_float_array(points, true);
        id<MTLBuffer> centroidsBuf = create_buffer_from_float_array(centroids, true);
        id<MTLBuffer> lossesBuf = [device newBufferWithLength:n * sizeof(float)
                                                      options:MTLResourceStorageModeShared];

        uint32_t d32 = (uint32_t)d;
        uint32_t k32 = (uint32_t)k;

        // Encode and dispatch
        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:pointsBuf offset:0 atIndex:0];
        [encoder setBuffer:centroidsBuf offset:0 atIndex:1];
        [encoder setBuffer:lossesBuf offset:0 atIndex:2];
        [encoder setBytes:&d32 length:sizeof(d32) atIndex:3];
        [encoder setBytes:&k32 length:sizeof(k32) atIndex:4];

        MTLSize gridSize = MTLSizeMake(n, 1, 1);
        NSUInteger threadGroupSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, n);
        MTLSize threadgroupSize = MTLSizeMake(threadGroupSize, 1, 1);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:threadgroupSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        // Sum up losses on CPU (could do GPU reduction too)
        float* losses = (float*)[lossesBuf contents];
        double totalLoss = 0.0;
        for (size_t i = 0; i < n; i++) {
            totalLoss += losses[i];
        }

        return totalLoss;
    }
}

// Matrix-vector multiply on GPU: y = A * x
LEAN_EXPORT lean_obj_res scilean_metal_gemv(
    size_t m, size_t n,
    b_lean_obj_arg A,
    b_lean_obj_arg x
) {
    if (!ensure_metal_initialized()) {
        return lean_box(0); // Return empty on failure
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"gemv");
        if (!pipeline) return lean_box(0);

        id<MTLBuffer> Abuf = create_buffer_from_float_array(A, true);
        id<MTLBuffer> xbuf = create_buffer_from_float_array(x, true);
        id<MTLBuffer> ybuf = [device newBufferWithLength:m * sizeof(float)
                                                 options:MTLResourceStorageModeShared];

        uint32_t n32 = (uint32_t)n;

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:Abuf offset:0 atIndex:0];
        [encoder setBuffer:xbuf offset:0 atIndex:1];
        [encoder setBuffer:ybuf offset:0 atIndex:2];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:3];

        MTLSize gridSize = MTLSizeMake(m, 1, 1);
        NSUInteger threadGroupSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, m);
        MTLSize threadgroupSize = MTLSizeMake(threadGroupSize, 1, 1);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:threadgroupSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_float_array(ybuf, m);
    }
}

// Matrix multiply on GPU: C = A * B
LEAN_EXPORT lean_obj_res scilean_metal_gemm(
    size_t m, size_t k, size_t n,
    b_lean_obj_arg A,
    b_lean_obj_arg B
) {
    if (!ensure_metal_initialized()) {
        return lean_box(0);
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"gemm");
        if (!pipeline) return lean_box(0);

        id<MTLBuffer> Abuf = create_buffer_from_float_array(A, true);
        id<MTLBuffer> Bbuf = create_buffer_from_float_array(B, true);
        id<MTLBuffer> Cbuf = [device newBufferWithLength:m * n * sizeof(float)
                                                 options:MTLResourceStorageModeShared];

        uint32_t m32 = (uint32_t)m;
        uint32_t k32 = (uint32_t)k;
        uint32_t n32 = (uint32_t)n;

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:Abuf offset:0 atIndex:0];
        [encoder setBuffer:Bbuf offset:0 atIndex:1];
        [encoder setBuffer:Cbuf offset:0 atIndex:2];
        [encoder setBytes:&m32 length:sizeof(m32) atIndex:3];
        [encoder setBytes:&k32 length:sizeof(k32) atIndex:4];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:5];

        MTLSize gridSize = MTLSizeMake(n, m, 1);
        MTLSize threadgroupSize = MTLSizeMake(16, 16, 1);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:threadgroupSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_float_array(Cbuf, m * n);
    }
}

// Tiled GEMM on GPU: C = A * B (optimized with shared memory)
// Uses 32x32 tiles for better cache reuse
LEAN_EXPORT lean_obj_res scilean_metal_gemm_tiled(
    size_t m, size_t k, size_t n,
    b_lean_obj_arg A,
    b_lean_obj_arg B
) {
    if (!ensure_metal_initialized()) {
        return lean_box(0);
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"gemm_tiled");
        if (!pipeline) return lean_box(0);

        id<MTLBuffer> Abuf = create_buffer_from_float_array(A, true);
        id<MTLBuffer> Bbuf = create_buffer_from_float_array(B, true);
        id<MTLBuffer> Cbuf = [device newBufferWithLength:m * n * sizeof(float)
                                                 options:MTLResourceStorageModeShared];

        uint32_t m32 = (uint32_t)m;
        uint32_t k32 = (uint32_t)k;
        uint32_t n32 = (uint32_t)n;

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:Abuf offset:0 atIndex:0];
        [encoder setBuffer:Bbuf offset:0 atIndex:1];
        [encoder setBuffer:Cbuf offset:0 atIndex:2];
        [encoder setBytes:&m32 length:sizeof(m32) atIndex:3];
        [encoder setBytes:&k32 length:sizeof(k32) atIndex:4];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:5];

        // Tiled dispatch: 32x32 threads per threadgroup
        const NSUInteger TILE_SIZE = 32;
        MTLSize threadgroupSize = MTLSizeMake(TILE_SIZE, TILE_SIZE, 1);
        MTLSize numThreadgroups = MTLSizeMake(
            (n + TILE_SIZE - 1) / TILE_SIZE,
            (m + TILE_SIZE - 1) / TILE_SIZE,
            1);

        [encoder dispatchThreadgroups:numThreadgroups threadsPerThreadgroup:threadgroupSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_float_array(Cbuf, m * n);
    }
}

// Simdgroup GEMM on GPU: C = A * B (using Apple's hardware matrix units)
// Uses simdgroup_matrix for 8×8 cooperative operations
LEAN_EXPORT lean_obj_res scilean_metal_gemm_simd(
    size_t m, size_t k, size_t n,
    b_lean_obj_arg A,
    b_lean_obj_arg B
) {
    if (!ensure_metal_initialized()) {
        return lean_box(0);
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"gemm_simd");
        if (!pipeline) return lean_box(0);

        id<MTLBuffer> Abuf = create_buffer_from_float_array(A, true);
        id<MTLBuffer> Bbuf = create_buffer_from_float_array(B, true);
        id<MTLBuffer> Cbuf = [device newBufferWithLength:m * n * sizeof(float)
                                                 options:MTLResourceStorageModeShared];

        uint32_t m32 = (uint32_t)m;
        uint32_t k32 = (uint32_t)k;
        uint32_t n32 = (uint32_t)n;

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:Abuf offset:0 atIndex:0];
        [encoder setBuffer:Bbuf offset:0 atIndex:1];
        [encoder setBuffer:Cbuf offset:0 atIndex:2];
        [encoder setBytes:&m32 length:sizeof(m32) atIndex:3];
        [encoder setBytes:&k32 length:sizeof(k32) atIndex:4];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:5];

        // Simdgroup dispatch: 32×32 output tile per threadgroup, 4 simdgroups (128 threads)
        const NSUInteger SIMD_TILE_M = 32;
        const NSUInteger SIMD_TILE_N = 32;
        MTLSize threadgroupSize = MTLSizeMake(32, 4, 1);  // 4 simdgroups × 32 threads each
        MTLSize numThreadgroups = MTLSizeMake(
            (n + SIMD_TILE_N - 1) / SIMD_TILE_N,
            (m + SIMD_TILE_M - 1) / SIMD_TILE_M,
            1);

        [encoder dispatchThreadgroups:numThreadgroups threadsPerThreadgroup:threadgroupSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_float_array(Cbuf, m * n);
    }
}

// Element-wise add on GPU
LEAN_EXPORT lean_obj_res scilean_metal_add(
    size_t n,
    b_lean_obj_arg a,
    b_lean_obj_arg b
) {
    if (!ensure_metal_initialized()) {
        return lean_box(0);
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"add");
        if (!pipeline) return lean_box(0);

        id<MTLBuffer> abuf = create_buffer_from_float_array(a, true);
        id<MTLBuffer> bbuf = create_buffer_from_float_array(b, true);
        id<MTLBuffer> cbuf = [device newBufferWithLength:n * sizeof(float)
                                                 options:MTLResourceStorageModeShared];

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:abuf offset:0 atIndex:0];
        [encoder setBuffer:bbuf offset:0 atIndex:1];
        [encoder setBuffer:cbuf offset:0 atIndex:2];

        MTLSize gridSize = MTLSizeMake(n, 1, 1);
        NSUInteger threadGroupSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, n);
        MTLSize threadgroupSize = MTLSizeMake(threadGroupSize, 1, 1);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:threadgroupSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_float_array(cbuf, n);
    }
}

// Check if Metal is available
LEAN_EXPORT uint8_t scilean_metal_available() {
    return ensure_metal_initialized() ? 1 : 0;
}

// ============================================================
// Generic Unary Operations
// ============================================================

static lean_obj_res run_unary_op(const char* kernelName, size_t n, b_lean_obj_arg x) {
    if (!ensure_metal_initialized()) {
        return lean_box(0);
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline([NSString stringWithUTF8String:kernelName]);
        if (!pipeline) return lean_box(0);

        id<MTLBuffer> xbuf = create_buffer_from_float_array(x, true);
        id<MTLBuffer> ybuf = [device newBufferWithLength:n * sizeof(float)
                                                 options:MTLResourceStorageModeShared];

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:xbuf offset:0 atIndex:0];
        [encoder setBuffer:ybuf offset:0 atIndex:1];

        MTLSize gridSize = MTLSizeMake(n, 1, 1);
        NSUInteger threadGroupSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, n);
        MTLSize threadgroupSize = MTLSizeMake(threadGroupSize, 1, 1);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:threadgroupSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_float_array(ybuf, n);
    }
}

LEAN_EXPORT lean_obj_res scilean_metal_neg(size_t n, b_lean_obj_arg x) {
    return run_unary_op("neg", n, x);
}

LEAN_EXPORT lean_obj_res scilean_metal_exp(size_t n, b_lean_obj_arg x) {
    return run_unary_op("exp_op", n, x);
}

LEAN_EXPORT lean_obj_res scilean_metal_exp2(size_t n, b_lean_obj_arg x) {
    return run_unary_op("exp2_op", n, x);
}

LEAN_EXPORT lean_obj_res scilean_metal_log(size_t n, b_lean_obj_arg x) {
    return run_unary_op("log_op", n, x);
}

LEAN_EXPORT lean_obj_res scilean_metal_log2(size_t n, b_lean_obj_arg x) {
    return run_unary_op("log2_op", n, x);
}

LEAN_EXPORT lean_obj_res scilean_metal_sin(size_t n, b_lean_obj_arg x) {
    return run_unary_op("sin_op", n, x);
}

LEAN_EXPORT lean_obj_res scilean_metal_cos(size_t n, b_lean_obj_arg x) {
    return run_unary_op("cos_op", n, x);
}

LEAN_EXPORT lean_obj_res scilean_metal_sqrt(size_t n, b_lean_obj_arg x) {
    return run_unary_op("sqrt_op", n, x);
}

LEAN_EXPORT lean_obj_res scilean_metal_reciprocal(size_t n, b_lean_obj_arg x) {
    return run_unary_op("reciprocal", n, x);
}

LEAN_EXPORT lean_obj_res scilean_metal_relu(size_t n, b_lean_obj_arg x) {
    return run_unary_op("relu", n, x);
}

LEAN_EXPORT lean_obj_res scilean_metal_sigmoid(size_t n, b_lean_obj_arg x) {
    return run_unary_op("sigmoid", n, x);
}

LEAN_EXPORT lean_obj_res scilean_metal_tanh(size_t n, b_lean_obj_arg x) {
    return run_unary_op("tanh_op", n, x);
}

// ============================================================
// Generic Binary Operations
// ============================================================

static lean_obj_res run_binary_op(const char* kernelName, size_t n, b_lean_obj_arg a, b_lean_obj_arg b) {
    if (!ensure_metal_initialized()) {
        return lean_box(0);
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline([NSString stringWithUTF8String:kernelName]);
        if (!pipeline) return lean_box(0);

        id<MTLBuffer> abuf = create_buffer_from_float_array(a, true);
        id<MTLBuffer> bbuf = create_buffer_from_float_array(b, true);
        id<MTLBuffer> cbuf = [device newBufferWithLength:n * sizeof(float)
                                                 options:MTLResourceStorageModeShared];

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:abuf offset:0 atIndex:0];
        [encoder setBuffer:bbuf offset:0 atIndex:1];
        [encoder setBuffer:cbuf offset:0 atIndex:2];

        MTLSize gridSize = MTLSizeMake(n, 1, 1);
        NSUInteger threadGroupSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, n);
        MTLSize threadgroupSize = MTLSizeMake(threadGroupSize, 1, 1);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:threadgroupSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_float_array(cbuf, n);
    }
}

LEAN_EXPORT lean_obj_res scilean_metal_sub(size_t n, b_lean_obj_arg a, b_lean_obj_arg b) {
    return run_binary_op("sub", n, a, b);
}

LEAN_EXPORT lean_obj_res scilean_metal_mul(size_t n, b_lean_obj_arg a, b_lean_obj_arg b) {
    return run_binary_op("mul", n, a, b);
}

LEAN_EXPORT lean_obj_res scilean_metal_div(size_t n, b_lean_obj_arg a, b_lean_obj_arg b) {
    return run_binary_op("div_op", n, a, b);
}

LEAN_EXPORT lean_obj_res scilean_metal_max(size_t n, b_lean_obj_arg a, b_lean_obj_arg b) {
    return run_binary_op("max_op", n, a, b);
}

LEAN_EXPORT lean_obj_res scilean_metal_min(size_t n, b_lean_obj_arg a, b_lean_obj_arg b) {
    return run_binary_op("min_op", n, a, b);
}

// ============================================================
// Reduction Operations
// ============================================================

LEAN_EXPORT double scilean_metal_reduce_sum(size_t n, b_lean_obj_arg x) {
    if (!ensure_metal_initialized()) {
        return 0.0;
    }

    @autoreleasepool {
        id<MTLBuffer> xbuf = create_buffer_from_float_array(x, true);

        // For small arrays, use single-pass reduction
        if (n <= 1024) {
            id<MTLComputePipelineState> pipeline = get_pipeline(@"reduce_sum");
            if (!pipeline) return 0.0;

            id<MTLBuffer> outbuf = [device newBufferWithLength:sizeof(float)
                                                       options:MTLResourceStorageModeShared];

            uint32_t n32 = (uint32_t)n;
            NSUInteger threadGroupSize = MIN(1024, n);

            id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
            id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

            [encoder setComputePipelineState:pipeline];
            [encoder setBuffer:xbuf offset:0 atIndex:0];
            [encoder setBuffer:outbuf offset:0 atIndex:1];
            [encoder setBytes:&n32 length:sizeof(n32) atIndex:2];
            [encoder setThreadgroupMemoryLength:threadGroupSize * sizeof(float) atIndex:0];

            MTLSize gridSize = MTLSizeMake(threadGroupSize, 1, 1);
            MTLSize tgSize = MTLSizeMake(threadGroupSize, 1, 1);

            [encoder dispatchThreads:gridSize threadsPerThreadgroup:tgSize];
            [encoder endEncoding];

            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];

            float* result = (float*)[outbuf contents];
            return (double)result[0];
        }

        // For large arrays, use two-pass reduction
        id<MTLComputePipelineState> pass1Pipeline = get_pipeline(@"reduce_sum_large");
        id<MTLComputePipelineState> pass2Pipeline = get_pipeline(@"reduce_sum");
        if (!pass1Pipeline || !pass2Pipeline) return 0.0;

        // Pass 1: reduce to partial sums (one per threadgroup)
        const NSUInteger BLOCK_SIZE = 256;
        NSUInteger numBlocks = MIN(256, (n + BLOCK_SIZE - 1) / BLOCK_SIZE);

        id<MTLBuffer> partialsBuf = [device newBufferWithLength:numBlocks * sizeof(float)
                                                        options:MTLResourceStorageModeShared];

        uint32_t n32 = (uint32_t)n;
        uint32_t numBlocks32 = (uint32_t)numBlocks;

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pass1Pipeline];
        [encoder setBuffer:xbuf offset:0 atIndex:0];
        [encoder setBuffer:partialsBuf offset:0 atIndex:1];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:2];
        [encoder setBytes:&numBlocks32 length:sizeof(numBlocks32) atIndex:3];

        MTLSize gridSize = MTLSizeMake(numBlocks * BLOCK_SIZE, 1, 1);
        MTLSize tgSize = MTLSizeMake(BLOCK_SIZE, 1, 1);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:tgSize];
        [encoder endEncoding];

        // Pass 2: reduce partial sums to final result
        id<MTLBuffer> outbuf = [device newBufferWithLength:sizeof(float)
                                                   options:MTLResourceStorageModeShared];

        encoder = [commandBuffer computeCommandEncoder];
        [encoder setComputePipelineState:pass2Pipeline];
        [encoder setBuffer:partialsBuf offset:0 atIndex:0];
        [encoder setBuffer:outbuf offset:0 atIndex:1];
        [encoder setBytes:&numBlocks32 length:sizeof(numBlocks32) atIndex:2];
        [encoder setThreadgroupMemoryLength:numBlocks * sizeof(float) atIndex:0];

        MTLSize gridSize2 = MTLSizeMake(numBlocks, 1, 1);
        MTLSize tgSize2 = MTLSizeMake(numBlocks, 1, 1);

        [encoder dispatchThreads:gridSize2 threadsPerThreadgroup:tgSize2];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        float* result = (float*)[outbuf contents];
        return (double)result[0];
    }
}

LEAN_EXPORT double scilean_metal_reduce_max(size_t n, b_lean_obj_arg x) {
    if (!ensure_metal_initialized()) {
        return -INFINITY;
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"reduce_max");
        if (!pipeline) return -INFINITY;

        id<MTLBuffer> xbuf = create_buffer_from_float_array(x, true);
        id<MTLBuffer> outbuf = [device newBufferWithLength:sizeof(float)
                                                   options:MTLResourceStorageModeShared];

        uint32_t n32 = (uint32_t)n;
        NSUInteger threadGroupSize = MIN(1024, n);

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:xbuf offset:0 atIndex:0];
        [encoder setBuffer:outbuf offset:0 atIndex:1];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:2];
        [encoder setThreadgroupMemoryLength:threadGroupSize * sizeof(float) atIndex:0];

        MTLSize gridSize = MTLSizeMake(threadGroupSize, 1, 1);
        MTLSize tgSize = MTLSizeMake(threadGroupSize, 1, 1);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:tgSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        float* result = (float*)[outbuf contents];
        return (double)result[0];
    }
}

LEAN_EXPORT double scilean_metal_reduce_min(size_t n, b_lean_obj_arg x) {
    if (!ensure_metal_initialized()) {
        return INFINITY;
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"reduce_min");
        if (!pipeline) return INFINITY;

        id<MTLBuffer> xbuf = create_buffer_from_float_array(x, true);
        id<MTLBuffer> outbuf = [device newBufferWithLength:sizeof(float)
                                                   options:MTLResourceStorageModeShared];

        uint32_t n32 = (uint32_t)n;
        NSUInteger threadGroupSize = MIN(1024, n);

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:xbuf offset:0 atIndex:0];
        [encoder setBuffer:outbuf offset:0 atIndex:1];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:2];
        [encoder setThreadgroupMemoryLength:threadGroupSize * sizeof(float) atIndex:0];

        MTLSize gridSize = MTLSizeMake(threadGroupSize, 1, 1);
        MTLSize tgSize = MTLSizeMake(threadGroupSize, 1, 1);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:tgSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        float* result = (float*)[outbuf contents];
        return (double)result[0];
    }
}

// ============================================================
// Fill Operations
// ============================================================

LEAN_EXPORT lean_obj_res scilean_metal_fill(size_t n, double value) {
    if (!ensure_metal_initialized()) {
        return lean_box(0);
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"fill_const");
        if (!pipeline) return lean_box(0);

        id<MTLBuffer> xbuf = [device newBufferWithLength:n * sizeof(float)
                                                 options:MTLResourceStorageModeShared];

        float val = (float)value;

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:xbuf offset:0 atIndex:0];
        [encoder setBytes:&val length:sizeof(val) atIndex:1];

        MTLSize gridSize = MTLSizeMake(n, 1, 1);
        NSUInteger threadGroupSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, n);
        MTLSize threadgroupSize = MTLSizeMake(threadGroupSize, 1, 1);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:threadgroupSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_float_array(xbuf, n);
    }
}

// ============================================================
// Float32 Operations (Native - No Conversion)
// ByteArray directly contains float data
// ============================================================

// Helper: Create Metal buffer directly from ByteArray (no conversion needed!)
static id<MTLBuffer> create_buffer_from_byte_array_f32(b_lean_obj_arg arr, size_t count, bool readonly) {
    float* data = (float*)lean_sarray_cptr(arr);
    MTLResourceOptions options = readonly ?
        MTLResourceStorageModeShared | MTLResourceCPUCacheModeDefaultCache :
        MTLResourceStorageModeShared;
    // Direct copy - no conversion!
    id<MTLBuffer> buffer = [device newBufferWithBytes:data
                                               length:count * sizeof(float)
                                              options:options];
    return buffer;
}

// Helper: Copy Metal buffer to new ByteArray
static lean_obj_res buffer_to_byte_array_f32(id<MTLBuffer> buffer, size_t count) {
    lean_obj_res arr = lean_alloc_sarray(1, count * sizeof(float), count * sizeof(float));
    float* metal_data = (float*)[buffer contents];
    float* lean_data = (float*)lean_sarray_cptr(arr);
    memcpy(lean_data, metal_data, count * sizeof(float));
    return arr;
}

// Simdgroup GEMM (Float32) - using Apple's hardware matrix units
LEAN_EXPORT lean_obj_res scilean_metal_gemm_simd_f32(
    size_t m, size_t k, size_t n,
    b_lean_obj_arg A,
    b_lean_obj_arg B
) {
    if (!ensure_metal_initialized()) {
        return lean_box(0);
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"gemm_simd");
        if (!pipeline) return lean_box(0);

        id<MTLBuffer> Abuf = create_buffer_from_byte_array_f32(A, m * k, true);
        id<MTLBuffer> Bbuf = create_buffer_from_byte_array_f32(B, k * n, true);
        id<MTLBuffer> Cbuf = [device newBufferWithLength:m * n * sizeof(float)
                                                 options:MTLResourceStorageModeShared];

        uint32_t m32 = (uint32_t)m;
        uint32_t k32 = (uint32_t)k;
        uint32_t n32 = (uint32_t)n;

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:Abuf offset:0 atIndex:0];
        [encoder setBuffer:Bbuf offset:0 atIndex:1];
        [encoder setBuffer:Cbuf offset:0 atIndex:2];
        [encoder setBytes:&m32 length:sizeof(m32) atIndex:3];
        [encoder setBytes:&k32 length:sizeof(k32) atIndex:4];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:5];

        // 4 simdgroups of 32 threads each = 128 threads per threadgroup
        const NSUInteger SIMD_TILE_M = 32;
        const NSUInteger SIMD_TILE_N = 32;
        MTLSize threadgroupSize = MTLSizeMake(32, 4, 1);  // 32 threads x 4 simdgroups
        MTLSize numThreadgroups = MTLSizeMake(
            (n + SIMD_TILE_N - 1) / SIMD_TILE_N,
            (m + SIMD_TILE_M - 1) / SIMD_TILE_M,
            1);

        [encoder dispatchThreadgroups:numThreadgroups threadsPerThreadgroup:threadgroupSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(Cbuf, m * n);
    }
}

// Fill (Float32)
LEAN_EXPORT lean_obj_res scilean_metal_fill_f32(size_t n, b_lean_obj_arg value_box) {
    if (!ensure_metal_initialized()) {
        return lean_box(0);
    }

    float value = lean_unbox_float32(value_box);

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"fill_const");
        if (!pipeline) return lean_box(0);

        id<MTLBuffer> xbuf = [device newBufferWithLength:n * sizeof(float)
                                                 options:MTLResourceStorageModeShared];

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:xbuf offset:0 atIndex:0];
        [encoder setBytes:&value length:sizeof(value) atIndex:1];

        MTLSize gridSize = MTLSizeMake(n, 1, 1);
        NSUInteger threadGroupSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, n);
        MTLSize threadgroupSize = MTLSizeMake(threadGroupSize, 1, 1);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:threadgroupSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(xbuf, n);
    }
}

// Unary op macro for Float32
#define METAL_UNARY_OP_F32(name, kernel) \
LEAN_EXPORT lean_obj_res scilean_metal_##name##_f32(size_t n, b_lean_obj_arg x) { \
    if (!ensure_metal_initialized()) return lean_box(0); \
    @autoreleasepool { \
        id<MTLComputePipelineState> pipeline = get_pipeline(@kernel); \
        if (!pipeline) return lean_box(0); \
        id<MTLBuffer> xbuf = create_buffer_from_byte_array_f32(x, n, true); \
        id<MTLBuffer> outbuf = [device newBufferWithLength:n * sizeof(float) \
                                                   options:MTLResourceStorageModeShared]; \
        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer]; \
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder]; \
        [encoder setComputePipelineState:pipeline]; \
        [encoder setBuffer:xbuf offset:0 atIndex:0]; \
        [encoder setBuffer:outbuf offset:0 atIndex:1]; \
        MTLSize gridSize = MTLSizeMake(n, 1, 1); \
        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, n); \
        [encoder dispatchThreads:gridSize threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)]; \
        [encoder endEncoding]; \
        [commandBuffer commit]; \
        [commandBuffer waitUntilCompleted]; \
        return buffer_to_byte_array_f32(outbuf, n); \
    } \
}

METAL_UNARY_OP_F32(neg, "neg")
METAL_UNARY_OP_F32(exp2, "exp2_op")
METAL_UNARY_OP_F32(log2, "log2_op")
METAL_UNARY_OP_F32(sin, "sin_op")
METAL_UNARY_OP_F32(sqrt, "sqrt_op")
METAL_UNARY_OP_F32(reciprocal, "reciprocal")

// Binary op macro for Float32
#define METAL_BINARY_OP_F32(name, kernel) \
LEAN_EXPORT lean_obj_res scilean_metal_##name##_f32(size_t n, b_lean_obj_arg a, b_lean_obj_arg b) { \
    if (!ensure_metal_initialized()) return lean_box(0); \
    @autoreleasepool { \
        id<MTLComputePipelineState> pipeline = get_pipeline(@kernel); \
        if (!pipeline) return lean_box(0); \
        id<MTLBuffer> abuf = create_buffer_from_byte_array_f32(a, n, true); \
        id<MTLBuffer> bbuf = create_buffer_from_byte_array_f32(b, n, true); \
        id<MTLBuffer> outbuf = [device newBufferWithLength:n * sizeof(float) \
                                                   options:MTLResourceStorageModeShared]; \
        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer]; \
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder]; \
        [encoder setComputePipelineState:pipeline]; \
        [encoder setBuffer:abuf offset:0 atIndex:0]; \
        [encoder setBuffer:bbuf offset:0 atIndex:1]; \
        [encoder setBuffer:outbuf offset:0 atIndex:2]; \
        MTLSize gridSize = MTLSizeMake(n, 1, 1); \
        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, n); \
        [encoder dispatchThreads:gridSize threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)]; \
        [encoder endEncoding]; \
        [commandBuffer commit]; \
        [commandBuffer waitUntilCompleted]; \
        return buffer_to_byte_array_f32(outbuf, n); \
    } \
}

METAL_BINARY_OP_F32(add, "add")
METAL_BINARY_OP_F32(sub, "sub")
METAL_BINARY_OP_F32(mul, "mul")
METAL_BINARY_OP_F32(div, "div_op")
METAL_BINARY_OP_F32(max, "max_op")
METAL_BINARY_OP_F32(min, "min_op")

// Reduce sum (Float32)
LEAN_EXPORT lean_obj_res scilean_metal_reduce_sum_f32(size_t n, b_lean_obj_arg x) {
    if (!ensure_metal_initialized()) {
        return lean_box_float32(0.0f);
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"reduce_sum");
        if (!pipeline) return lean_box_float32(0.0f);

        id<MTLBuffer> xbuf = create_buffer_from_byte_array_f32(x, n, true);
        id<MTLBuffer> outbuf = [device newBufferWithLength:sizeof(float)
                                                   options:MTLResourceStorageModeShared];

        uint32_t n32 = (uint32_t)n;
        NSUInteger threadGroupSize = MIN(1024, n);

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:xbuf offset:0 atIndex:0];
        [encoder setBuffer:outbuf offset:0 atIndex:1];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:2];
        [encoder setThreadgroupMemoryLength:threadGroupSize * sizeof(float) atIndex:0];

        MTLSize gridSize = MTLSizeMake(threadGroupSize, 1, 1);
        MTLSize tgSize = MTLSizeMake(threadGroupSize, 1, 1);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:tgSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        float* result = (float*)[outbuf contents];
        return lean_box_float32(result[0]);
    }
}

// Reduce max (Float32)
LEAN_EXPORT lean_obj_res scilean_metal_reduce_max_f32(size_t n, b_lean_obj_arg x) {
    if (!ensure_metal_initialized()) {
        return lean_box_float32(-INFINITY);
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"reduce_max");
        if (!pipeline) return lean_box_float32(-INFINITY);

        id<MTLBuffer> xbuf = create_buffer_from_byte_array_f32(x, n, true);
        id<MTLBuffer> outbuf = [device newBufferWithLength:sizeof(float)
                                                   options:MTLResourceStorageModeShared];

        uint32_t n32 = (uint32_t)n;
        NSUInteger threadGroupSize = MIN(1024, n);

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:xbuf offset:0 atIndex:0];
        [encoder setBuffer:outbuf offset:0 atIndex:1];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:2];
        [encoder setThreadgroupMemoryLength:threadGroupSize * sizeof(float) atIndex:0];

        MTLSize gridSize = MTLSizeMake(threadGroupSize, 1, 1);
        MTLSize tgSize = MTLSizeMake(threadGroupSize, 1, 1);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:tgSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        float* result = (float*)[outbuf contents];
        return lean_box_float32(result[0]);
    }
}

// Reduce min (Float32)
LEAN_EXPORT lean_obj_res scilean_metal_reduce_min_f32(size_t n, b_lean_obj_arg x) {
    if (!ensure_metal_initialized()) {
        return lean_box_float32(INFINITY);
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"reduce_min");
        if (!pipeline) return lean_box_float32(INFINITY);

        id<MTLBuffer> xbuf = create_buffer_from_byte_array_f32(x, n, true);
        id<MTLBuffer> outbuf = [device newBufferWithLength:sizeof(float)
                                                   options:MTLResourceStorageModeShared];

        uint32_t n32 = (uint32_t)n;
        NSUInteger threadGroupSize = MIN(1024, n);

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:xbuf offset:0 atIndex:0];
        [encoder setBuffer:outbuf offset:0 atIndex:1];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:2];
        [encoder setThreadgroupMemoryLength:threadGroupSize * sizeof(float) atIndex:0];

        MTLSize gridSize = MTLSizeMake(threadGroupSize, 1, 1);
        MTLSize tgSize = MTLSizeMake(threadGroupSize, 1, 1);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:tgSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        float* result = (float*)[outbuf contents];
        return lean_box_float32(result[0]);
    }
}

// GEMM (Float32) - Matrix multiply C = A * B
LEAN_EXPORT lean_obj_res scilean_metal_gemm_f32(size_t m, size_t k, size_t n,
                                                 b_lean_obj_arg A, b_lean_obj_arg B) {
    if (!ensure_metal_initialized()) {
        return lean_box(0);
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"gemm");
        if (!pipeline) return lean_box(0);

        id<MTLBuffer> Abuf = create_buffer_from_byte_array_f32(A, m * k, true);
        id<MTLBuffer> Bbuf = create_buffer_from_byte_array_f32(B, k * n, true);
        id<MTLBuffer> Cbuf = [device newBufferWithLength:m * n * sizeof(float)
                                                 options:MTLResourceStorageModeShared];

        uint32_t m32 = (uint32_t)m;
        uint32_t k32 = (uint32_t)k;
        uint32_t n32 = (uint32_t)n;

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:Abuf offset:0 atIndex:0];
        [encoder setBuffer:Bbuf offset:0 atIndex:1];
        [encoder setBuffer:Cbuf offset:0 atIndex:2];
        [encoder setBytes:&m32 length:sizeof(m32) atIndex:3];
        [encoder setBytes:&k32 length:sizeof(k32) atIndex:4];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:5];

        MTLSize gridSize = MTLSizeMake(n, m, 1);
        NSUInteger w = pipeline.threadExecutionWidth;
        NSUInteger h = pipeline.maxTotalThreadsPerThreadgroup / w;
        MTLSize threadgroupSize = MTLSizeMake(w, h, 1);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:threadgroupSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(Cbuf, m * n);
    }
}

// Tiled GEMM (Float32) - Matrix multiply C = A * B with shared memory
LEAN_EXPORT lean_obj_res scilean_metal_gemm_tiled_f32(size_t m, size_t k, size_t n,
                                                       b_lean_obj_arg A, b_lean_obj_arg B) {
    if (!ensure_metal_initialized()) {
        return lean_box(0);
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"gemm_tiled");
        if (!pipeline) return lean_box(0);

        id<MTLBuffer> Abuf = create_buffer_from_byte_array_f32(A, m * k, true);
        id<MTLBuffer> Bbuf = create_buffer_from_byte_array_f32(B, k * n, true);
        id<MTLBuffer> Cbuf = [device newBufferWithLength:m * n * sizeof(float)
                                                 options:MTLResourceStorageModeShared];

        uint32_t m32 = (uint32_t)m;
        uint32_t k32 = (uint32_t)k;
        uint32_t n32 = (uint32_t)n;

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:Abuf offset:0 atIndex:0];
        [encoder setBuffer:Bbuf offset:0 atIndex:1];
        [encoder setBuffer:Cbuf offset:0 atIndex:2];
        [encoder setBytes:&m32 length:sizeof(m32) atIndex:3];
        [encoder setBytes:&k32 length:sizeof(k32) atIndex:4];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:5];

        // Tiled dispatch: 32x32 threads per threadgroup
        const NSUInteger TILE_SIZE = 32;
        MTLSize threadgroupSize = MTLSizeMake(TILE_SIZE, TILE_SIZE, 1);
        MTLSize numThreadgroups = MTLSizeMake(
            (n + TILE_SIZE - 1) / TILE_SIZE,
            (m + TILE_SIZE - 1) / TILE_SIZE,
            1);

        [encoder dispatchThreadgroups:numThreadgroups threadsPerThreadgroup:threadgroupSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(Cbuf, m * n);
    }
}

// ============================================================
// MPS GEMM (Apple's highly optimized implementation)
// ============================================================
// Uses Metal Performance Shaders for maximum performance
// This leverages Apple's hand-tuned matrix multiplication

LEAN_EXPORT lean_obj_res scilean_metal_gemm_mps_f32(
    size_t m, size_t k, size_t n,
    b_lean_obj_arg A,
    b_lean_obj_arg B
) {
    if (!ensure_metal_initialized()) {
        return lean_alloc_sarray(1, 0, 0);
    }

    @autoreleasepool {
        // Create buffers
        id<MTLBuffer> Abuf = create_buffer_from_byte_array_f32(A, m * k, true);
        id<MTLBuffer> Bbuf = create_buffer_from_byte_array_f32(B, k * n, true);
        id<MTLBuffer> Cbuf = [device newBufferWithLength:m * n * sizeof(float)
                                                 options:MTLResourceStorageModeShared];

        // Create MPS matrix descriptors
        // Row bytes = number of columns * sizeof(float)
        MPSMatrixDescriptor* descA = [MPSMatrixDescriptor
            matrixDescriptorWithRows:m
            columns:k
            rowBytes:k * sizeof(float)
            dataType:MPSDataTypeFloat32];

        MPSMatrixDescriptor* descB = [MPSMatrixDescriptor
            matrixDescriptorWithRows:k
            columns:n
            rowBytes:n * sizeof(float)
            dataType:MPSDataTypeFloat32];

        MPSMatrixDescriptor* descC = [MPSMatrixDescriptor
            matrixDescriptorWithRows:m
            columns:n
            rowBytes:n * sizeof(float)
            dataType:MPSDataTypeFloat32];

        // Create MPS matrices
        MPSMatrix* matA = [[MPSMatrix alloc] initWithBuffer:Abuf descriptor:descA];
        MPSMatrix* matB = [[MPSMatrix alloc] initWithBuffer:Bbuf descriptor:descB];
        MPSMatrix* matC = [[MPSMatrix alloc] initWithBuffer:Cbuf descriptor:descC];

        // Create matrix multiplication kernel
        // C = alpha * A * B + beta * C
        // We want C = A * B, so alpha = 1.0, beta = 0.0
        MPSMatrixMultiplication* matMul = [[MPSMatrixMultiplication alloc]
            initWithDevice:device
            transposeLeft:false
            transposeRight:false
            resultRows:m
            resultColumns:n
            interiorColumns:k
            alpha:1.0
            beta:0.0];

        // Execute
        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        [matMul encodeToCommandBuffer:commandBuffer
                           leftMatrix:matA
                          rightMatrix:matB
                         resultMatrix:matC];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(Cbuf, m * n);
    }
}

// ============================================================
// AXPY and Fused Operations (Float32)
// ============================================================

// Helper: return empty ByteArray on error
static lean_obj_res empty_byte_array_f32() {
    return lean_alloc_sarray(1, 0, 0);
}

// AXPY (Float32): y = a*x + y
// All parameters as ByteArray for zero-copy FFI
LEAN_EXPORT lean_obj_res scilean_metal_axpy_f32(
    size_t n,
    b_lean_obj_arg a_arr,  // scalar as ByteArray[4]
    b_lean_obj_arg x,
    b_lean_obj_arg y
) {
    if (!ensure_metal_initialized() || n == 0) {
        return empty_byte_array_f32();
    }

    // Read scalar directly from ByteArray pointer - zero copy
    float a = ((float*)lean_sarray_cptr(a_arr))[0];

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"axpy");
        if (!pipeline) return empty_byte_array_f32();

        id<MTLBuffer> xbuf = create_buffer_from_byte_array_f32(x, n, true);
        id<MTLBuffer> ybuf = create_buffer_from_byte_array_f32(y, n, false);
        if (!xbuf || !ybuf) return empty_byte_array_f32();

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:xbuf offset:0 atIndex:0];
        [encoder setBuffer:ybuf offset:0 atIndex:1];
        [encoder setBytes:&a length:sizeof(a) atIndex:2];
        uint32_t n32 = (uint32_t)n;
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:3];

        // Use dispatchThreadgroups with bounds checking in kernel
        const NSUInteger threadGroupSize = 256;
        NSUInteger numThreadgroups = (n + threadGroupSize - 1) / threadGroupSize;
        MTLSize threadgroupSizeObj = MTLSizeMake(threadGroupSize, 1, 1);
        MTLSize numThreadgroupsObj = MTLSizeMake(numThreadgroups, 1, 1);

        [encoder dispatchThreadgroups:numThreadgroupsObj threadsPerThreadgroup:threadgroupSizeObj];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(ybuf, n);
    }
}

// AXPBY (Float32): z = a*x + b*y
// All parameters as ByteArray for zero-copy FFI
LEAN_EXPORT lean_obj_res scilean_metal_axpby_f32(
    size_t n,
    b_lean_obj_arg a_arr,  // scalar as ByteArray[4]
    b_lean_obj_arg x,
    b_lean_obj_arg b_arr,  // scalar as ByteArray[4]
    b_lean_obj_arg y
) {
    if (!ensure_metal_initialized() || n == 0) {
        return empty_byte_array_f32();
    }

    // Read scalars directly from ByteArray pointers - zero copy
    float a = ((float*)lean_sarray_cptr(a_arr))[0];
    float b = ((float*)lean_sarray_cptr(b_arr))[0];

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"axpby");
        if (!pipeline) return empty_byte_array_f32();

        id<MTLBuffer> xbuf = create_buffer_from_byte_array_f32(x, n, true);
        id<MTLBuffer> ybuf = create_buffer_from_byte_array_f32(y, n, true);
        if (!xbuf || !ybuf) return empty_byte_array_f32();

        id<MTLBuffer> zbuf = [device newBufferWithLength:n * sizeof(float)
                                                 options:MTLResourceStorageModeShared];

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:xbuf offset:0 atIndex:0];
        [encoder setBuffer:ybuf offset:0 atIndex:1];
        [encoder setBuffer:zbuf offset:0 atIndex:2];
        [encoder setBytes:&a length:sizeof(a) atIndex:3];
        [encoder setBytes:&b length:sizeof(b) atIndex:4];

        MTLSize gridSize = MTLSizeMake(n, 1, 1);
        NSUInteger threadGroupSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, n);
        MTLSize threadgroupSize = MTLSizeMake(threadGroupSize, 1, 1);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:threadgroupSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(zbuf, n);
    }
}

// Softmax (Float32) - fused implementation
// Uses 3 passes: 1) find max, 2) compute exp and sum, 3) normalize
LEAN_EXPORT lean_obj_res scilean_metal_softmax_f32(
    size_t n,
    b_lean_obj_arg x
) {
    if (!ensure_metal_initialized()) {
        return empty_byte_array_f32();
    }

    @autoreleasepool {
        // Step 1: Find max using reduce_max_large
        id<MTLComputePipelineState> reduceMaxPipeline = get_pipeline(@"reduce_max_large");
        id<MTLComputePipelineState> softmaxPass1Pipeline = get_pipeline(@"softmax_fused_pass1");
        id<MTLComputePipelineState> reduceSumPipeline = get_pipeline(@"reduce_sum");
        id<MTLComputePipelineState> normalizePipeline = get_pipeline(@"softmax_normalize");
        if (!reduceMaxPipeline || !softmaxPass1Pipeline || !reduceSumPipeline || !normalizePipeline) {
            NSLog(@"Softmax: Failed to get one or more pipelines");
            return empty_byte_array_f32();
        }

        id<MTLBuffer> inputBuf = create_buffer_from_byte_array_f32(x, n, true);
        id<MTLBuffer> outputBuf = [device newBufferWithLength:n * sizeof(float)
                                                      options:MTLResourceStorageModeShared];

        // Compute number of threadgroups for reductions
        const NSUInteger blockSize = 256;
        NSUInteger numBlocks = (n + blockSize - 1) / blockSize;
        numBlocks = MIN(numBlocks, 256);  // Limit to 256 blocks

        id<MTLBuffer> partialsBuf = [device newBufferWithLength:numBlocks * sizeof(float)
                                                        options:MTLResourceStorageModeShared];
        id<MTLBuffer> resultBuf = [device newBufferWithLength:sizeof(float)
                                                      options:MTLResourceStorageModeShared];

        uint32_t n32 = (uint32_t)n;
        uint32_t numBlocks32 = (uint32_t)numBlocks;

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        // Pass 1a: Find max value
        [encoder setComputePipelineState:reduceMaxPipeline];
        [encoder setBuffer:inputBuf offset:0 atIndex:0];
        [encoder setBuffer:partialsBuf offset:0 atIndex:1];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:2];
        [encoder setBytes:&numBlocks32 length:sizeof(numBlocks32) atIndex:3];
        [encoder dispatchThreadgroups:MTLSizeMake(numBlocks, 1, 1)
                threadsPerThreadgroup:MTLSizeMake(blockSize, 1, 1)];

        // Pass 1b: Final reduction for max
        [encoder setComputePipelineState:reduceSumPipeline];  // reusing reduce structure
        [encoder setBuffer:partialsBuf offset:0 atIndex:0];
        [encoder setBuffer:resultBuf offset:0 atIndex:1];
        [encoder setBytes:&numBlocks32 length:sizeof(numBlocks32) atIndex:2];
        [encoder setThreadgroupMemoryLength:numBlocks * sizeof(float) atIndex:0];
        [encoder dispatchThreadgroups:MTLSizeMake(1, 1, 1)
                threadsPerThreadgroup:MTLSizeMake(MIN(numBlocks, blockSize), 1, 1)];

        [encoder endEncoding];
        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        // Read max value
        float maxVal = ((float*)[resultBuf contents])[0];

        // Pass 2: Compute exp(x - max) and partial sums
        commandBuffer = [commandQueue commandBuffer];
        encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:softmaxPass1Pipeline];
        [encoder setBuffer:inputBuf offset:0 atIndex:0];
        [encoder setBuffer:outputBuf offset:0 atIndex:1];
        [encoder setBuffer:partialsBuf offset:0 atIndex:2];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:3];
        [encoder setBytes:&maxVal length:sizeof(maxVal) atIndex:4];
        [encoder dispatchThreadgroups:MTLSizeMake(numBlocks, 1, 1)
                threadsPerThreadgroup:MTLSizeMake(blockSize, 1, 1)];

        // Pass 2b: Final sum reduction
        [encoder setComputePipelineState:reduceSumPipeline];
        [encoder setBuffer:partialsBuf offset:0 atIndex:0];
        [encoder setBuffer:resultBuf offset:0 atIndex:1];
        [encoder setBytes:&numBlocks32 length:sizeof(numBlocks32) atIndex:2];
        [encoder setThreadgroupMemoryLength:numBlocks * sizeof(float) atIndex:0];
        [encoder dispatchThreadgroups:MTLSizeMake(1, 1, 1)
                threadsPerThreadgroup:MTLSizeMake(MIN(numBlocks, blockSize), 1, 1)];

        [encoder endEncoding];
        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        // Read sum value
        float sumVal = ((float*)[resultBuf contents])[0];

        // Pass 3: Normalize
        commandBuffer = [commandQueue commandBuffer];
        encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:normalizePipeline];
        [encoder setBuffer:outputBuf offset:0 atIndex:0];
        [encoder setBytes:&sumVal length:sizeof(sumVal) atIndex:1];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:2];

        MTLSize gridSize = MTLSizeMake(n, 1, 1);
        NSUInteger tgSize = MIN(normalizePipeline.maxTotalThreadsPerThreadgroup, n);
        [encoder dispatchThreads:gridSize threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)];

        [encoder endEncoding];
        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(outputBuf, n);
    }
}

// ============================================================
// Accelerate Framework GEMM (CPU/AMX)
// Uses Apple's vDSP/BLAS which leverages AMX on Apple Silicon
// ============================================================

// Accelerate GEMM (Float32): Uses CPU AMX units
// This is Apple's optimized BLAS implementation that uses AMX coprocessor
LEAN_EXPORT lean_obj_res scilean_accelerate_gemm_f32(
    size_t m, size_t k, size_t n,
    b_lean_obj_arg A,
    b_lean_obj_arg B
) {
    // Allocate output
    lean_obj_res C = lean_alloc_sarray(1, m * n * sizeof(float), m * n * sizeof(float));

    float* aData = (float*)lean_sarray_cptr(A);
    float* bData = (float*)lean_sarray_cptr(B);
    float* cData = (float*)lean_sarray_cptr(C);

    // Initialize C to zero
    memset(cData, 0, m * n * sizeof(float));

    // cblas_sgemm: C = alpha*A*B + beta*C
    // Row-major layout (CblasRowMajor)
    // A is m×k, B is k×n, C is m×n
    cblas_sgemm(
        CblasRowMajor,  // Row-major storage
        CblasNoTrans,   // Don't transpose A
        CblasNoTrans,   // Don't transpose B
        (int)m,         // Rows of A and C
        (int)n,         // Columns of B and C
        (int)k,         // Columns of A, rows of B
        1.0f,           // alpha
        aData,          // A
        (int)k,         // Leading dimension of A
        bData,          // B
        (int)n,         // Leading dimension of B
        0.0f,           // beta
        cData,          // C
        (int)n          // Leading dimension of C
    );

    return C;
}

} // extern "C"
