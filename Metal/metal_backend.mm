#import <Metal/Metal.h>
#import <Foundation/Foundation.h>
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

// Create a Metal buffer from a Lean FloatArray
static id<MTLBuffer> create_buffer_from_float_array(b_lean_obj_arg arr, bool readonly) {
    size_t size = lean_sarray_size(arr) * sizeof(float);
    float* data = (float*)lean_sarray_cptr(arr);

    MTLResourceOptions options = readonly ?
        MTLResourceStorageModeShared | MTLResourceCPUCacheModeDefaultCache :
        MTLResourceStorageModeShared;

    return [device newBufferWithBytes:data length:size options:options];
}

// Copy Metal buffer back to Lean FloatArray
static lean_obj_res buffer_to_float_array(id<MTLBuffer> buffer, size_t count) {
    lean_obj_res arr = lean_alloc_sarray(sizeof(float), count, count);
    memcpy(lean_sarray_cptr(arr), [buffer contents], count * sizeof(float));
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

} // extern "C"
