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

// Buffer pool for reducing allocation overhead
// Buckets: 256B, 1KB, 4KB, 16KB, 64KB, 256KB, 1MB, 4MB, 16MB
static const size_t BUFFER_BUCKET_SIZES[] = {256, 1024, 4096, 16384, 65536, 262144, 1048576, 4194304, 16777216};
static const size_t NUM_BUFFER_BUCKETS = sizeof(BUFFER_BUCKET_SIZES) / sizeof(BUFFER_BUCKET_SIZES[0]);
static const size_t MAX_POOLED_BUFFERS_PER_BUCKET = 4;
static NSMutableArray<id<MTLBuffer>>* bufferPool[NUM_BUFFER_BUCKETS] = {nil};

// ============================================================================
// Command Buffer Batching
// ============================================================================
// When batching is enabled, operations queue into a shared command buffer
// instead of creating individual buffers. Call batch_begin() to start,
// batch_execute() to submit all queued operations at once.
// This eliminates per-op synchronization overhead (10-50μs per op).

static bool g_batch_mode = false;
static id<MTLCommandBuffer> g_batch_command_buffer = nil;
static id<MTLComputeCommandEncoder> g_batch_encoder = nil;
static NSMutableArray<id<MTLBuffer>>* g_batch_outputs = nil;  // Track outputs for lifetime

static bool is_batch_mode() {
    return g_batch_mode && g_batch_encoder != nil;
}

static id<MTLComputeCommandEncoder> get_encoder_for_op() {
    if (is_batch_mode()) {
        return g_batch_encoder;
    }
    // Non-batched: create new command buffer and encoder
    id<MTLCommandBuffer> cb = [commandQueue commandBuffer];
    return [cb computeCommandEncoder];
}

static size_t get_buffer_bucket(size_t size) {
    for (size_t i = 0; i < NUM_BUFFER_BUCKETS; i++) {
        if (size <= BUFFER_BUCKET_SIZES[i]) return i;
    }
    return NUM_BUFFER_BUCKETS; // Too large for pool
}

static id<MTLBuffer> get_pooled_buffer(size_t size) {
    size_t bucket = get_buffer_bucket(size);
    if (bucket >= NUM_BUFFER_BUCKETS) {
        // Too large, allocate directly
        return [device newBufferWithLength:size options:MTLResourceStorageModeShared];
    }

    NSMutableArray* pool = bufferPool[bucket];
    if (pool && pool.count > 0) {
        id<MTLBuffer> buffer = [pool lastObject];
        [pool removeLastObject];
        return buffer;
    }

    // Allocate new buffer of bucket size
    return [device newBufferWithLength:BUFFER_BUCKET_SIZES[bucket] options:MTLResourceStorageModeShared];
}

static void return_pooled_buffer(id<MTLBuffer> buffer) {
    if (!buffer) return;

    size_t bucket = get_buffer_bucket(buffer.length);
    if (bucket >= NUM_BUFFER_BUCKETS) return; // Don't pool large buffers

    if (!bufferPool[bucket]) {
        bufferPool[bucket] = [NSMutableArray arrayWithCapacity:MAX_POOLED_BUFFERS_PER_BUCKET];
    }

    if (bufferPool[bucket].count < MAX_POOLED_BUFFERS_PER_BUCKET) {
        [bufferPool[bucket] addObject:buffer];
    }
    // Otherwise let ARC release it
}

// ============================================================================
// GpuBuffer: GPU-Resident Buffer Type
// ============================================================================
// This is the key optimization: data stays on GPU between operations,
// eliminating the copy overhead that dominates small/medium operations.

// GpuBuffer structure - wraps a Metal buffer with size info
typedef struct {
    id<MTLBuffer> buffer;  // The actual Metal buffer (retained by ARC)
    size_t size_bytes;     // Size in bytes
} GpuBufferData;

// Lean external class for GpuBuffer
static void gpu_buffer_finalize(void* ptr) {
    GpuBufferData* data = (GpuBufferData*)ptr;
    if (data) {
        // Return buffer to pool if small enough, otherwise release
        if (data->buffer) {
            return_pooled_buffer(data->buffer);
            data->buffer = nil;
        }
        free(data);
    }
}

static void gpu_buffer_foreach(void* ptr, b_lean_obj_arg f) {
    // No nested Lean objects to traverse
}

static lean_external_class* g_gpu_buffer_class = nullptr;

static lean_external_class* get_gpu_buffer_class() {
    if (!g_gpu_buffer_class) {
        g_gpu_buffer_class = lean_register_external_class(
            gpu_buffer_finalize,
            gpu_buffer_foreach
        );
    }
    return g_gpu_buffer_class;
}

// Create a Lean GpuBuffer object from a Metal buffer
static lean_obj_res wrap_gpu_buffer(id<MTLBuffer> buffer, size_t size_bytes) {
    GpuBufferData* data = (GpuBufferData*)malloc(sizeof(GpuBufferData));
    data->buffer = buffer;  // ARC retains
    data->size_bytes = size_bytes;
    return lean_alloc_external(get_gpu_buffer_class(), data);
}

// Extract Metal buffer from Lean GpuBuffer object
static GpuBufferData* unwrap_gpu_buffer(b_lean_obj_arg obj) {
    return (GpuBufferData*)lean_get_external_data(obj);
}

// Helper: Get Metal buffer from GpuBuffer
static id<MTLBuffer> get_mtl_buffer(b_lean_obj_arg obj) {
    GpuBufferData* data = unwrap_gpu_buffer(obj);
    return data ? data->buffer : nil;
}

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

// ============================================================================
// Batch API FFI Functions
// ============================================================================

// Begin a batch of GPU operations
// All subsequent GPU ops will queue into a shared command buffer
LEAN_EXPORT lean_obj_res scilean_gpu_batch_begin(lean_obj_arg /* world */) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    if (g_batch_mode) {
        // Already in batch mode - this is a nested call, just return success
        return lean_io_result_mk_ok(lean_box(0));
    }

    @autoreleasepool {
        g_batch_command_buffer = [commandQueue commandBuffer];
        g_batch_encoder = [g_batch_command_buffer computeCommandEncoder];
        g_batch_outputs = [NSMutableArray array];
        g_batch_mode = true;
    }

    return lean_io_result_mk_ok(lean_box(0));
}

// Execute all batched GPU operations and wait for completion
LEAN_EXPORT lean_obj_res scilean_gpu_batch_execute(lean_obj_arg /* world */) {
    if (!g_batch_mode || !g_batch_encoder) {
        return lean_io_result_mk_error(lean_mk_string("Not in batch mode"));
    }

    @autoreleasepool {
        [g_batch_encoder endEncoding];
        [g_batch_command_buffer commit];
        [g_batch_command_buffer waitUntilCompleted];

        // Clear batch state
        g_batch_encoder = nil;
        g_batch_command_buffer = nil;
        g_batch_outputs = nil;
        g_batch_mode = false;
    }

    return lean_io_result_mk_ok(lean_box(0));
}

// Cancel batch mode without executing (useful for error handling)
LEAN_EXPORT lean_obj_res scilean_gpu_batch_cancel(lean_obj_arg /* world */) {
    @autoreleasepool {
        if (g_batch_encoder) {
            [g_batch_encoder endEncoding];
        }
        // Don't commit - just discard
        g_batch_encoder = nil;
        g_batch_command_buffer = nil;
        g_batch_outputs = nil;
        g_batch_mode = false;
    }

    return lean_io_result_mk_ok(lean_box(0));
}

// Check if currently in batch mode
LEAN_EXPORT uint8_t scilean_gpu_is_batch_mode() {
    return g_batch_mode ? 1 : 0;
}

// ============================================================================
// GpuBuffer FFI Functions
// ============================================================================

// Allocate uninitialized GPU buffer
LEAN_EXPORT lean_obj_res scilean_gpu_alloc_f32(size_t num_floats, lean_obj_arg /* world */) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    size_t size_bytes = num_floats * sizeof(float);
    id<MTLBuffer> buffer = get_pooled_buffer(size_bytes);
    if (!buffer) {
        buffer = [device newBufferWithLength:size_bytes options:MTLResourceStorageModeShared];
    }

    lean_obj_res gpu_buf = wrap_gpu_buffer(buffer, size_bytes);
    return lean_io_result_mk_ok(gpu_buf);
}

// Upload ByteArray to GPU
LEAN_EXPORT lean_obj_res scilean_gpu_upload_f32(b_lean_obj_arg data, lean_obj_arg /* world */) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    size_t size_bytes = lean_sarray_byte_size(data);
    const void* src = lean_sarray_cptr(data);

    // Allocate GPU buffer
    id<MTLBuffer> buffer = get_pooled_buffer(size_bytes);
    if (!buffer) {
        buffer = [device newBufferWithLength:size_bytes options:MTLResourceStorageModeShared];
    }

    // Copy data to GPU
    memcpy(buffer.contents, src, size_bytes);

    lean_obj_res gpu_buf = wrap_gpu_buffer(buffer, size_bytes);
    return lean_io_result_mk_ok(gpu_buf);
}

// Download GPU buffer to ByteArray
LEAN_EXPORT lean_obj_res scilean_gpu_download_f32(b_lean_obj_arg buf, lean_obj_arg /* world */) {
    GpuBufferData* data = unwrap_gpu_buffer(buf);
    if (!data || !data->buffer) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    size_t size_bytes = data->size_bytes;
    lean_obj_res arr = lean_alloc_sarray(1, size_bytes, size_bytes);
    memcpy(lean_sarray_cptr(arr), data->buffer.contents, size_bytes);

    return lean_io_result_mk_ok(arr);
}

// Get size in bytes
LEAN_EXPORT size_t scilean_gpu_size(b_lean_obj_arg buf) {
    GpuBufferData* data = unwrap_gpu_buffer(buf);
    return data ? data->size_bytes : 0;
}

// Free GPU buffer (optional - will be freed by GC)
LEAN_EXPORT lean_obj_res scilean_gpu_free(lean_obj_arg buf, lean_obj_arg /* world */) {
    // Just let Lean's GC handle it by decrementing refcount
    lean_dec(buf);
    return lean_io_result_mk_ok(lean_box(0));
}

// Slice a GPU buffer: returns a new buffer containing elements [offset, offset + count)
// This is a GPU-to-GPU copy, not a view (safer memory management)
LEAN_EXPORT lean_obj_res scilean_gpu_slice_f32(
    b_lean_obj_arg src_buf,
    size_t offset_floats,
    size_t count_floats,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    GpuBufferData* src_data = unwrap_gpu_buffer(src_buf);
    if (!src_data || !src_data->buffer) {
        return lean_io_result_mk_error(lean_mk_string("Invalid source GpuBuffer"));
    }

    size_t offset_bytes = offset_floats * sizeof(float);
    size_t size_bytes = count_floats * sizeof(float);

    // Bounds check
    if (offset_bytes + size_bytes > src_data->size_bytes) {
        return lean_io_result_mk_error(lean_mk_string("Slice out of bounds"));
    }

    // Allocate destination buffer
    id<MTLBuffer> dst_buffer = get_pooled_buffer(size_bytes);
    if (!dst_buffer) {
        dst_buffer = [device newBufferWithLength:size_bytes options:MTLResourceStorageModeShared];
    }

    // Copy the slice (shared storage allows CPU access)
    const char* src_ptr = (const char*)src_data->buffer.contents + offset_bytes;
    memcpy(dst_buffer.contents, src_ptr, size_bytes);

    lean_obj_res gpu_buf = wrap_gpu_buffer(dst_buffer, size_bytes);
    return lean_io_result_mk_ok(gpu_buf);
}

// ============================================================================
// GPU-to-GPU Operations (No CPU Copies!)
// ============================================================================

// GEMM on GPU buffers: C = A * B
// Supports batching: when in batch mode, queues to shared command buffer
LEAN_EXPORT lean_obj_res scilean_gpu_gemm_f32(
    b_lean_obj_arg A_buf,
    b_lean_obj_arg B_buf,
    size_t m, size_t k, size_t n,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> A = get_mtl_buffer(A_buf);
    id<MTLBuffer> B = get_mtl_buffer(B_buf);
    if (!A || !B) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        // Use optimized double-buffered kernel for better performance
        id<MTLComputePipelineState> pipeline = get_pipeline(@"gemm_simd_opt");
        bool use_opt = (pipeline != nil);

        if (!use_opt) {
            // Fall back to safe kernel
            pipeline = get_pipeline(@"gemm_simd_safe");
            if (!pipeline) {
                return lean_io_result_mk_error(lean_mk_string("Failed to get GEMM pipeline"));
            }
        }

        size_t output_size = m * n * sizeof(float);
        id<MTLBuffer> C = get_pooled_buffer(output_size);
        if (!C) {
            C = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        uint32_t m32 = (uint32_t)m;
        uint32_t k32 = (uint32_t)k;
        uint32_t n32 = (uint32_t)n;

        // Use batch encoder if in batch mode, otherwise create new command buffer
        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:A offset:0 atIndex:0];
        [encoder setBuffer:B offset:0 atIndex:1];
        [encoder setBuffer:C offset:0 atIndex:2];
        [encoder setBytes:&m32 length:sizeof(m32) atIndex:3];
        [encoder setBytes:&k32 length:sizeof(k32) atIndex:4];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:5];

        if (use_opt) {
            // Optimized kernel: 64x64 output tiles, 256 threads (8 simdgroups)
            // Threadgroup memory: As[2][64][32] + Bs[2][32][64] = 8192 floats = 32KB
            size_t tg_mem_size = 8192 * sizeof(float);
            [encoder setThreadgroupMemoryLength:tg_mem_size atIndex:0];

            MTLSize gridSize = MTLSizeMake((n + 63) / 64, (m + 63) / 64, 1);
            MTLSize tgSize = MTLSizeMake(256, 1, 1);  // 8 simdgroups × 32 threads
            [encoder dispatchThreadgroups:gridSize threadsPerThreadgroup:tgSize];
        } else {
            // Safe kernel: 32x32 output tiles, 128 threads (4 simdgroups)
            size_t tg_mem_size = 1024 * sizeof(float);
            [encoder setThreadgroupMemoryLength:tg_mem_size atIndex:0];

            MTLSize gridSize = MTLSizeMake((n + 31) / 32, (m + 31) / 32, 1);
            MTLSize tgSize = MTLSizeMake(128, 1, 1);
            [encoder dispatchThreadgroups:gridSize threadsPerThreadgroup:tgSize];
        }

        // Only commit if not in batch mode
        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            // Track output buffer for lifetime in batch mode
            [g_batch_outputs addObject:C];
        }

        lean_obj_res result = wrap_gpu_buffer(C, output_size);
        return lean_io_result_mk_ok(result);
    }
}

// Fused GEMM + Bias + ReLU: C = max(0, A @ B + bias)
// Supports batching: when in batch mode, queues to shared command buffer
LEAN_EXPORT lean_obj_res scilean_gpu_gemm_bias_relu_f32(
    b_lean_obj_arg A_buf,
    b_lean_obj_arg B_buf,
    b_lean_obj_arg bias_buf,
    size_t m, size_t k, size_t n,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> A = get_mtl_buffer(A_buf);
    id<MTLBuffer> B = get_mtl_buffer(B_buf);
    id<MTLBuffer> bias = get_mtl_buffer(bias_buf);
    if (!A || !B || !bias) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        // Use simd version for larger matrices, tiled for smaller
        bool use_simd = (m >= 32 && n >= 32);
        id<MTLComputePipelineState> pipeline = get_pipeline(use_simd ? @"gemm_bias_relu_simd" : @"gemm_bias_relu");
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get gemm_bias_relu pipeline"));
        }

        size_t output_size = m * n * sizeof(float);
        id<MTLBuffer> C = get_pooled_buffer(output_size);
        if (!C) {
            C = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        uint32_t m32 = (uint32_t)m;
        uint32_t k32 = (uint32_t)k;
        uint32_t n32 = (uint32_t)n;

        // Use batch encoder if in batch mode
        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:A offset:0 atIndex:0];
        [encoder setBuffer:B offset:0 atIndex:1];
        [encoder setBuffer:bias offset:0 atIndex:2];
        [encoder setBuffer:C offset:0 atIndex:3];
        [encoder setBytes:&m32 length:sizeof(m32) atIndex:4];
        [encoder setBytes:&k32 length:sizeof(k32) atIndex:5];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:6];

        MTLSize gridSize, tgSize;
        if (use_simd) {
            gridSize = MTLSizeMake((n + 31) / 32, (m + 31) / 32, 1);
            tgSize = MTLSizeMake(32, 4, 1);
            [encoder dispatchThreadgroups:gridSize threadsPerThreadgroup:tgSize];
        } else {
            gridSize = MTLSizeMake((n + 31) / 32 * 32, (m + 31) / 32 * 32, 1);
            tgSize = MTLSizeMake(32, 32, 1);
            [encoder dispatchThreads:gridSize threadsPerThreadgroup:tgSize];
        }

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:C];
        }

        lean_obj_res result = wrap_gpu_buffer(C, output_size);
        return lean_io_result_mk_ok(result);
    }
}

// Element-wise add on GPU buffers
// Supports batching: when in batch mode, queues to shared command buffer
LEAN_EXPORT lean_obj_res scilean_gpu_add_f32(
    b_lean_obj_arg A_buf,
    b_lean_obj_arg B_buf,
    size_t n,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> A = get_mtl_buffer(A_buf);
    id<MTLBuffer> B = get_mtl_buffer(B_buf);
    if (!A || !B) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"add");
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get add pipeline"));
        }

        size_t output_size = n * sizeof(float);
        id<MTLBuffer> C = get_pooled_buffer(output_size);
        if (!C) {
            C = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        // Use batch encoder if in batch mode
        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:A offset:0 atIndex:0];
        [encoder setBuffer:B offset:0 atIndex:1];
        [encoder setBuffer:C offset:0 atIndex:2];

        MTLSize gridSize = MTLSizeMake(n, 1, 1);
        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, n);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)];

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:C];
        }

        lean_obj_res result = wrap_gpu_buffer(C, output_size);
        return lean_io_result_mk_ok(result);
    }
}

// Element-wise multiply on GPU buffers
// Supports batching: when in batch mode, queues to shared command buffer
LEAN_EXPORT lean_obj_res scilean_gpu_mul_f32(
    b_lean_obj_arg A_buf,
    b_lean_obj_arg B_buf,
    size_t n,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> A = get_mtl_buffer(A_buf);
    id<MTLBuffer> B = get_mtl_buffer(B_buf);
    if (!A || !B) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"mul");
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get mul pipeline"));
        }

        size_t output_size = n * sizeof(float);
        id<MTLBuffer> C = get_pooled_buffer(output_size);
        if (!C) {
            C = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        // Use batch encoder if in batch mode
        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:A offset:0 atIndex:0];
        [encoder setBuffer:B offset:0 atIndex:1];
        [encoder setBuffer:C offset:0 atIndex:2];

        MTLSize gridSize = MTLSizeMake(n, 1, 1);
        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, n);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)];

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:C];
        }

        lean_obj_res result = wrap_gpu_buffer(C, output_size);
        return lean_io_result_mk_ok(result);
    }
}

// ReLU on GPU buffer
// Supports batching: when in batch mode, queues to shared command buffer
LEAN_EXPORT lean_obj_res scilean_gpu_relu_f32(
    b_lean_obj_arg X_buf,
    size_t n,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> X = get_mtl_buffer(X_buf);
    if (!X) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"relu");
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get relu pipeline"));
        }

        size_t output_size = n * sizeof(float);
        id<MTLBuffer> Y = get_pooled_buffer(output_size);
        if (!Y) {
            Y = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        // Use batch encoder if in batch mode
        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:X offset:0 atIndex:0];
        [encoder setBuffer:Y offset:0 atIndex:1];

        MTLSize gridSize = MTLSizeMake(n, 1, 1);
        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, n);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)];

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:Y];
        }

        lean_obj_res result = wrap_gpu_buffer(Y, output_size);
        return lean_io_result_mk_ok(result);
    }
}

// Softmax on GPU buffer
// Supports batching: when in batch mode, queues to shared command buffer
LEAN_EXPORT lean_obj_res scilean_gpu_softmax_f32(
    b_lean_obj_arg X_buf,
    size_t num_rows, size_t row_size,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> X = get_mtl_buffer(X_buf);
    if (!X) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"softmax_batched");
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get softmax pipeline"));
        }

        size_t n = num_rows * row_size;
        size_t output_size = n * sizeof(float);
        id<MTLBuffer> Y = get_pooled_buffer(output_size);
        if (!Y) {
            Y = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        uint32_t row_size32 = (uint32_t)row_size;

        // Use batch encoder if in batch mode
        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:X offset:0 atIndex:0];
        [encoder setBuffer:Y offset:0 atIndex:1];
        [encoder setBytes:&row_size32 length:sizeof(row_size32) atIndex:2];

        // Allocate threadgroup memory for the shared array (one float per element in row)
        NSUInteger threadgroupMemorySize = row_size * sizeof(float);
        [encoder setThreadgroupMemoryLength:threadgroupMemorySize atIndex:0];

        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, row_size);

        [encoder dispatchThreadgroups:MTLSizeMake(num_rows, 1, 1)
                threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)];

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:Y];
        }

        lean_obj_res result = wrap_gpu_buffer(Y, output_size);
        return lean_io_result_mk_ok(result);
    }
}

// Conv2D on GPU buffers
LEAN_EXPORT lean_obj_res scilean_gpu_conv2d_f32(
    b_lean_obj_arg input_buf,
    b_lean_obj_arg kernel_buf,
    b_lean_obj_arg bias_buf,
    size_t batch_size,
    size_t in_channels,
    size_t out_channels,
    size_t in_height,
    size_t in_width,
    size_t kernel_h,
    size_t kernel_w,
    size_t stride_h,
    size_t stride_w,
    size_t pad_h,
    size_t pad_w,
    uint8_t use_relu,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> input = get_mtl_buffer(input_buf);
    id<MTLBuffer> kernel = get_mtl_buffer(kernel_buf);
    id<MTLBuffer> bias = get_mtl_buffer(bias_buf);
    if (!input || !kernel || !bias) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        // Use optimized 3x3 kernel when applicable
        bool use_3x3 = (kernel_h == 3 && kernel_w == 3 &&
                        stride_h == 1 && stride_w == 1 &&
                        pad_h == 1 && pad_w == 1);

        const char* kernel_name = use_3x3 ? "conv2d_3x3_winograd" : (use_relu ? "conv2d_relu" : "conv2d_naive");
        id<MTLComputePipelineState> pipeline = get_pipeline([NSString stringWithUTF8String:kernel_name]);
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get conv2d pipeline"));
        }

        size_t out_height = (in_height + 2 * pad_h - kernel_h) / stride_h + 1;
        size_t out_width = (in_width + 2 * pad_w - kernel_w) / stride_w + 1;
        size_t output_size = batch_size * out_channels * out_height * out_width * sizeof(float);

        id<MTLBuffer> output = get_pooled_buffer(output_size);
        if (!output) {
            output = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        // Use batch encoder if in batch mode
        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:input offset:0 atIndex:0];
        [encoder setBuffer:kernel offset:0 atIndex:1];
        [encoder setBuffer:bias offset:0 atIndex:2];
        [encoder setBuffer:output offset:0 atIndex:3];

        if (use_3x3) {
            uint32_t batch32 = (uint32_t)batch_size;
            uint32_t ic32 = (uint32_t)in_channels;
            uint32_t oc32 = (uint32_t)out_channels;
            uint32_t ih32 = (uint32_t)in_height;
            uint32_t iw32 = (uint32_t)in_width;
            uint32_t relu32 = (uint32_t)use_relu;

            [encoder setBytes:&batch32 length:sizeof(batch32) atIndex:4];
            [encoder setBytes:&ic32 length:sizeof(ic32) atIndex:5];
            [encoder setBytes:&oc32 length:sizeof(oc32) atIndex:6];
            [encoder setBytes:&ih32 length:sizeof(ih32) atIndex:7];
            [encoder setBytes:&iw32 length:sizeof(iw32) atIndex:8];
            [encoder setBytes:&relu32 length:sizeof(relu32) atIndex:9];
        } else {
            uint32_t batch32 = (uint32_t)batch_size;
            uint32_t ic32 = (uint32_t)in_channels;
            uint32_t oc32 = (uint32_t)out_channels;
            uint32_t ih32 = (uint32_t)in_height;
            uint32_t iw32 = (uint32_t)in_width;
            uint32_t kh32 = (uint32_t)kernel_h;
            uint32_t kw32 = (uint32_t)kernel_w;
            uint32_t sh32 = (uint32_t)stride_h;
            uint32_t sw32 = (uint32_t)stride_w;
            uint32_t ph32 = (uint32_t)pad_h;
            uint32_t pw32 = (uint32_t)pad_w;

            [encoder setBytes:&batch32 length:sizeof(batch32) atIndex:4];
            [encoder setBytes:&ic32 length:sizeof(ic32) atIndex:5];
            [encoder setBytes:&oc32 length:sizeof(oc32) atIndex:6];
            [encoder setBytes:&ih32 length:sizeof(ih32) atIndex:7];
            [encoder setBytes:&iw32 length:sizeof(iw32) atIndex:8];
            [encoder setBytes:&kh32 length:sizeof(kh32) atIndex:9];
            [encoder setBytes:&kw32 length:sizeof(kw32) atIndex:10];
            [encoder setBytes:&sh32 length:sizeof(sh32) atIndex:11];
            [encoder setBytes:&sw32 length:sizeof(sw32) atIndex:12];
            [encoder setBytes:&ph32 length:sizeof(ph32) atIndex:13];
            [encoder setBytes:&pw32 length:sizeof(pw32) atIndex:14];
        }

        MTLSize gridSize = MTLSizeMake(out_width, out_height, batch_size * out_channels);
        NSUInteger w = MIN(pipeline.maxTotalThreadsPerThreadgroup, 16);
        MTLSize tgSize = MTLSizeMake(w, w, 1);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:tgSize];

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:output];
        }

        lean_obj_res result = wrap_gpu_buffer(output, output_size);
        return lean_io_result_mk_ok(result);
    }
}

// MaxPool2D on GPU buffers
LEAN_EXPORT lean_obj_res scilean_gpu_maxpool2d_f32(
    b_lean_obj_arg input_buf,
    size_t batch_size,
    size_t channels,
    size_t in_height,
    size_t in_width,
    size_t pool_h,
    size_t pool_w,
    size_t stride_h,
    size_t stride_w,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> input = get_mtl_buffer(input_buf);
    if (!input) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"maxpool2d");
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get maxpool2d pipeline"));
        }

        size_t out_height = (in_height - pool_h) / stride_h + 1;
        size_t out_width = (in_width - pool_w) / stride_w + 1;
        size_t output_size = batch_size * channels * out_height * out_width * sizeof(float);

        id<MTLBuffer> output = get_pooled_buffer(output_size);
        if (!output) {
            output = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        uint32_t batch32 = (uint32_t)batch_size;
        uint32_t c32 = (uint32_t)channels;
        uint32_t ih32 = (uint32_t)in_height;
        uint32_t iw32 = (uint32_t)in_width;
        uint32_t ph32 = (uint32_t)pool_h;
        uint32_t pw32 = (uint32_t)pool_w;
        uint32_t sh32 = (uint32_t)stride_h;
        uint32_t sw32 = (uint32_t)stride_w;

        // Use batch encoder if in batch mode
        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:input offset:0 atIndex:0];
        [encoder setBuffer:output offset:0 atIndex:1];
        [encoder setBytes:&batch32 length:sizeof(batch32) atIndex:2];
        [encoder setBytes:&c32 length:sizeof(c32) atIndex:3];
        [encoder setBytes:&ih32 length:sizeof(ih32) atIndex:4];
        [encoder setBytes:&iw32 length:sizeof(iw32) atIndex:5];
        [encoder setBytes:&ph32 length:sizeof(ph32) atIndex:6];
        [encoder setBytes:&pw32 length:sizeof(pw32) atIndex:7];
        [encoder setBytes:&sh32 length:sizeof(sh32) atIndex:8];
        [encoder setBytes:&sw32 length:sizeof(sw32) atIndex:9];

        MTLSize gridSize = MTLSizeMake(out_width, out_height, batch_size * channels);
        NSUInteger w = MIN(pipeline.maxTotalThreadsPerThreadgroup, 16);
        MTLSize tgSize = MTLSizeMake(w, w, 1);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:tgSize];

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:output];
        }

        lean_obj_res result = wrap_gpu_buffer(output, output_size);
        return lean_io_result_mk_ok(result);
    }
}

// Bias + ReLU fused
LEAN_EXPORT lean_obj_res scilean_gpu_bias_relu_f32(
    b_lean_obj_arg X_buf,
    b_lean_obj_arg bias_buf,
    size_t n,
    size_t stride,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> X = get_mtl_buffer(X_buf);
    id<MTLBuffer> bias = get_mtl_buffer(bias_buf);
    if (!X || !bias) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"bias_relu");
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get bias_relu pipeline"));
        }

        size_t output_size = n * sizeof(float);
        id<MTLBuffer> Y = get_pooled_buffer(output_size);
        if (!Y) {
            Y = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        uint32_t n32 = (uint32_t)n;
        uint32_t stride32 = (uint32_t)stride;

        // Use batch encoder if in batch mode
        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:X offset:0 atIndex:0];
        [encoder setBuffer:bias offset:0 atIndex:1];
        [encoder setBuffer:Y offset:0 atIndex:2];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:3];
        [encoder setBytes:&stride32 length:sizeof(stride32) atIndex:4];

        MTLSize gridSize = MTLSizeMake(n, 1, 1);
        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, n);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)];

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:Y];
        }

        lean_obj_res result = wrap_gpu_buffer(Y, output_size);
        return lean_io_result_mk_ok(result);
    }
}

// Layer normalization on GPU buffers
// Supports batching: when in batch mode, queues to shared command buffer
// y = gamma * (x - mean) / sqrt(var + eps) + beta
LEAN_EXPORT lean_obj_res scilean_gpu_layer_norm_f32(
    b_lean_obj_arg X_buf,
    b_lean_obj_arg gamma_buf,
    b_lean_obj_arg beta_buf,
    size_t n,
    size_t hidden_size,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> X = get_mtl_buffer(X_buf);
    id<MTLBuffer> gamma = get_mtl_buffer(gamma_buf);
    id<MTLBuffer> beta = get_mtl_buffer(beta_buf);
    if (!X || !gamma || !beta) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"layer_norm");
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get layer_norm pipeline"));
        }

        size_t output_size = n * sizeof(float);
        id<MTLBuffer> Y = get_pooled_buffer(output_size);
        if (!Y) {
            Y = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        // The layer_norm kernel normalizes across hidden_size elements
        // n = total elements, hidden_size = normalization dimension
        // For now, kernel supports single group (hidden_size == n)
        uint32_t n32 = (uint32_t)hidden_size;  // The kernel param 'n' is the normalization dimension
        float eps = 1e-5f;

        // Use batch encoder if in batch mode
        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:X offset:0 atIndex:0];
        [encoder setBuffer:gamma offset:0 atIndex:1];
        [encoder setBuffer:beta offset:0 atIndex:2];
        [encoder setBuffer:Y offset:0 atIndex:3];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:4];
        [encoder setBytes:&eps length:sizeof(eps) atIndex:5];

        // Layer norm uses parallel reduction and requires exactly ONE threadgroup
        // with shared memory for reduction
        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, (NSUInteger)hidden_size);
        // Round up to power of 2 for reduction to work correctly
        NSUInteger powerOf2 = 1;
        while (powerOf2 < tgSize) powerOf2 *= 2;
        tgSize = MIN(powerOf2, pipeline.maxTotalThreadsPerThreadgroup);

        // Allocate threadgroup memory for reduction
        [encoder setThreadgroupMemoryLength:tgSize * sizeof(float) atIndex:0];

        // Dispatch exactly one threadgroup
        [encoder dispatchThreadgroups:MTLSizeMake(1, 1, 1)
                threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)];

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:Y];
        }

        lean_obj_res result = wrap_gpu_buffer(Y, output_size);
        return lean_io_result_mk_ok(result);
    }
}

// Bias + GELU fused operation on GPU buffers
// Supports batching: when in batch mode, queues to shared command buffer
// y = gelu(x + bias) where gelu(x) ≈ 0.5*x*(1+tanh(sqrt(2/pi)*(x+0.044715*x^3)))
LEAN_EXPORT lean_obj_res scilean_gpu_bias_gelu_f32(
    b_lean_obj_arg X_buf,
    b_lean_obj_arg bias_buf,
    size_t n,
    size_t stride,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> X = get_mtl_buffer(X_buf);
    id<MTLBuffer> bias = get_mtl_buffer(bias_buf);
    if (!X || !bias) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"bias_gelu");
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get bias_gelu pipeline"));
        }

        size_t output_size = n * sizeof(float);
        id<MTLBuffer> Y = get_pooled_buffer(output_size);
        if (!Y) {
            Y = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        uint32_t n32 = (uint32_t)n;
        uint32_t stride32 = (uint32_t)stride;

        // Use batch encoder if in batch mode
        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:X offset:0 atIndex:0];
        [encoder setBuffer:bias offset:0 atIndex:1];
        [encoder setBuffer:Y offset:0 atIndex:2];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:3];
        [encoder setBytes:&stride32 length:sizeof(stride32) atIndex:4];

        MTLSize gridSize = MTLSizeMake(n, 1, 1);
        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, n);
        [encoder dispatchThreads:gridSize threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)];

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:Y];
        }

        lean_obj_res result = wrap_gpu_buffer(Y, output_size);
        return lean_io_result_mk_ok(result);
    }
}

// Bias add (no activation) on GPU buffers
// Broadcasts bias across batch dimension: output[i] = input[i] + bias[i % stride]
// Used for output layer before softmax where we don't want activation
LEAN_EXPORT lean_obj_res scilean_gpu_bias_add_f32(
    b_lean_obj_arg X_buf,
    b_lean_obj_arg bias_buf,
    size_t n,
    size_t stride,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> X = get_mtl_buffer(X_buf);
    id<MTLBuffer> bias = get_mtl_buffer(bias_buf);
    if (!X || !bias) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"bias_add");
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get bias_add pipeline"));
        }

        size_t output_size = n * sizeof(float);
        id<MTLBuffer> Y = get_pooled_buffer(output_size);
        if (!Y) {
            Y = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        uint32_t n32 = (uint32_t)n;
        uint32_t stride32 = (uint32_t)stride;

        // Use batch encoder if in batch mode
        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:X offset:0 atIndex:0];
        [encoder setBuffer:bias offset:0 atIndex:1];
        [encoder setBuffer:Y offset:0 atIndex:2];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:3];
        [encoder setBytes:&stride32 length:sizeof(stride32) atIndex:4];

        MTLSize gridSize = MTLSizeMake(n, 1, 1);
        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, n);
        [encoder dispatchThreads:gridSize threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)];

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:Y];
        }

        lean_obj_res result = wrap_gpu_buffer(Y, output_size);
        return lean_io_result_mk_ok(result);
    }
}

// Average pooling 2D on GPU buffers
// Supports batching: when in batch mode, queues to shared command buffer
LEAN_EXPORT lean_obj_res scilean_gpu_avgpool2d_f32(
    b_lean_obj_arg X_buf,
    size_t batch_size,
    size_t channels,
    size_t in_height,
    size_t in_width,
    size_t pool_h,
    size_t pool_w,
    size_t stride_h,
    size_t stride_w,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> X = get_mtl_buffer(X_buf);
    if (!X) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"avgpool2d");
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get avgpool2d pipeline"));
        }

        size_t out_height = (in_height - pool_h) / stride_h + 1;
        size_t out_width = (in_width - pool_w) / stride_w + 1;
        size_t output_elements = batch_size * channels * out_height * out_width;
        size_t output_size = output_elements * sizeof(float);

        id<MTLBuffer> Y = get_pooled_buffer(output_size);
        if (!Y) {
            Y = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        uint32_t batch32 = (uint32_t)batch_size;
        uint32_t channels32 = (uint32_t)channels;
        uint32_t in_h32 = (uint32_t)in_height;
        uint32_t in_w32 = (uint32_t)in_width;
        uint32_t pool_h32 = (uint32_t)pool_h;
        uint32_t pool_w32 = (uint32_t)pool_w;
        uint32_t stride_h32 = (uint32_t)stride_h;
        uint32_t stride_w32 = (uint32_t)stride_w;

        // Use batch encoder if in batch mode
        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:X offset:0 atIndex:0];
        [encoder setBuffer:Y offset:0 atIndex:1];
        [encoder setBytes:&batch32 length:sizeof(batch32) atIndex:2];
        [encoder setBytes:&channels32 length:sizeof(channels32) atIndex:3];
        [encoder setBytes:&in_h32 length:sizeof(in_h32) atIndex:4];
        [encoder setBytes:&in_w32 length:sizeof(in_w32) atIndex:5];
        [encoder setBytes:&pool_h32 length:sizeof(pool_h32) atIndex:6];
        [encoder setBytes:&pool_w32 length:sizeof(pool_w32) atIndex:7];
        [encoder setBytes:&stride_h32 length:sizeof(stride_h32) atIndex:8];
        [encoder setBytes:&stride_w32 length:sizeof(stride_w32) atIndex:9];

        MTLSize gridSize = MTLSizeMake(out_width, out_height, batch_size * channels);
        MTLSize threadgroupSize = MTLSizeMake(
            MIN(16, out_width),
            MIN(16, out_height),
            1
        );
        [encoder dispatchThreads:gridSize threadsPerThreadgroup:threadgroupSize];

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:Y];
        }

        lean_obj_res result = wrap_gpu_buffer(Y, output_size);
        return lean_io_result_mk_ok(result);
    }
}

// Flash Attention on GPU buffers
// Supports batching: when in batch mode, queues to shared command buffer
// output = softmax(Q @ K^T / sqrt(head_dim)) @ V
LEAN_EXPORT lean_obj_res scilean_gpu_flash_attention_f32(
    b_lean_obj_arg Q_buf,
    b_lean_obj_arg K_buf,
    b_lean_obj_arg V_buf,
    size_t seq_len,
    size_t head_dim,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> Q = get_mtl_buffer(Q_buf);
    id<MTLBuffer> K = get_mtl_buffer(K_buf);
    id<MTLBuffer> V = get_mtl_buffer(V_buf);
    if (!Q || !K || !V) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"flash_attention");
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get flash_attention pipeline"));
        }

        size_t output_elements = seq_len * head_dim;
        size_t output_size = output_elements * sizeof(float);

        id<MTLBuffer> Y = get_pooled_buffer(output_size);
        if (!Y) {
            Y = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        uint32_t seq32 = (uint32_t)seq_len;
        uint32_t head32 = (uint32_t)head_dim;
        float scale = 1.0f / sqrtf((float)head_dim);

        // Use batch encoder if in batch mode
        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:Q offset:0 atIndex:0];
        [encoder setBuffer:K offset:0 atIndex:1];
        [encoder setBuffer:V offset:0 atIndex:2];
        [encoder setBuffer:Y offset:0 atIndex:3];
        [encoder setBytes:&seq32 length:sizeof(seq32) atIndex:4];
        [encoder setBytes:&head32 length:sizeof(head32) atIndex:5];
        [encoder setBytes:&scale length:sizeof(scale) atIndex:6];

        // One thread per query position
        MTLSize gridSize = MTLSizeMake(seq_len, 1, 1);
        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, seq_len);
        [encoder dispatchThreads:gridSize threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)];

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:Y];
        }

        lean_obj_res result = wrap_gpu_buffer(Y, output_size);
        return lean_io_result_mk_ok(result);
    }
}

// Flash Attention with causal mask on GPU buffers
// Supports batching: when in batch mode, queues to shared command buffer
// Applies causal masking: position i can only attend to positions <= i
LEAN_EXPORT lean_obj_res scilean_gpu_flash_attention_causal_f32(
    b_lean_obj_arg Q_buf,
    b_lean_obj_arg K_buf,
    b_lean_obj_arg V_buf,
    size_t seq_len,
    size_t head_dim,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> Q = get_mtl_buffer(Q_buf);
    id<MTLBuffer> K = get_mtl_buffer(K_buf);
    id<MTLBuffer> V = get_mtl_buffer(V_buf);
    if (!Q || !K || !V) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"flash_attention_causal");
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get flash_attention_causal pipeline"));
        }

        size_t output_elements = seq_len * head_dim;
        size_t output_size = output_elements * sizeof(float);

        id<MTLBuffer> Y = get_pooled_buffer(output_size);
        if (!Y) {
            Y = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        uint32_t seq32 = (uint32_t)seq_len;
        uint32_t head32 = (uint32_t)head_dim;
        float scale = 1.0f / sqrtf((float)head_dim);

        // Use batch encoder if in batch mode
        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:Q offset:0 atIndex:0];
        [encoder setBuffer:K offset:0 atIndex:1];
        [encoder setBuffer:V offset:0 atIndex:2];
        [encoder setBuffer:Y offset:0 atIndex:3];
        [encoder setBytes:&seq32 length:sizeof(seq32) atIndex:4];
        [encoder setBytes:&head32 length:sizeof(head32) atIndex:5];
        [encoder setBytes:&scale length:sizeof(scale) atIndex:6];

        // One thread per query position
        MTLSize gridSize = MTLSizeMake(seq_len, 1, 1);
        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, seq_len);
        [encoder dispatchThreads:gridSize threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)];

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:Y];
        }

        lean_obj_res result = wrap_gpu_buffer(Y, output_size);
        return lean_io_result_mk_ok(result);
    }
}

// GpuBuffer batchnorm2d (inference mode)
// Supports batching: when in batch mode, queues to shared command buffer
// apply_relu: if 1, applies ReLU after normalization (fused)
LEAN_EXPORT lean_obj_res scilean_gpu_batchnorm2d_f32(
    b_lean_obj_arg input_buf,
    b_lean_obj_arg gamma_buf,
    b_lean_obj_arg beta_buf,
    b_lean_obj_arg mean_buf,
    b_lean_obj_arg var_buf,
    size_t batch_size,
    size_t channels,
    size_t height,
    size_t width,
    double eps,
    size_t apply_relu,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> input = get_mtl_buffer(input_buf);
    id<MTLBuffer> gamma = get_mtl_buffer(gamma_buf);
    id<MTLBuffer> beta = get_mtl_buffer(beta_buf);
    id<MTLBuffer> mean = get_mtl_buffer(mean_buf);
    id<MTLBuffer> var = get_mtl_buffer(var_buf);
    if (!input || !gamma || !beta || !mean || !var) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"batchnorm2d_inference");
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get batchnorm2d_inference pipeline"));
        }

        size_t spatial_size = batch_size * channels * height * width;
        size_t output_size = spatial_size * sizeof(float);

        id<MTLBuffer> output = get_pooled_buffer(output_size);
        if (!output) {
            output = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        uint32_t batch32 = (uint32_t)batch_size;
        uint32_t c32 = (uint32_t)channels;
        uint32_t h32 = (uint32_t)height;
        uint32_t w32 = (uint32_t)width;
        float eps_f = (float)eps;
        uint32_t relu32 = (uint32_t)apply_relu;

        // Use batch encoder if in batch mode
        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:input offset:0 atIndex:0];
        [encoder setBuffer:gamma offset:0 atIndex:1];
        [encoder setBuffer:beta offset:0 atIndex:2];
        [encoder setBuffer:mean offset:0 atIndex:3];
        [encoder setBuffer:var offset:0 atIndex:4];
        [encoder setBuffer:output offset:0 atIndex:5];
        [encoder setBytes:&batch32 length:sizeof(batch32) atIndex:6];
        [encoder setBytes:&c32 length:sizeof(c32) atIndex:7];
        [encoder setBytes:&h32 length:sizeof(h32) atIndex:8];
        [encoder setBytes:&w32 length:sizeof(w32) atIndex:9];
        [encoder setBytes:&eps_f length:sizeof(eps_f) atIndex:10];
        [encoder setBytes:&relu32 length:sizeof(relu32) atIndex:11];

        // 3D grid: width × height × (batch_size * channels)
        MTLSize gridSize = MTLSizeMake(width, height, batch_size * channels);
        NSUInteger tgw = MIN(pipeline.maxTotalThreadsPerThreadgroup, 16);
        MTLSize threadgroupSize = MTLSizeMake(tgw, tgw, 1);
        [encoder dispatchThreads:gridSize threadsPerThreadgroup:threadgroupSize];

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:output];
        }

        lean_obj_res result = wrap_gpu_buffer(output, output_size);
        return lean_io_result_mk_ok(result);
    }
}

// ============================================================================
// Backward Pass Kernels for Autodiff
// ============================================================================

// ReLU backward: grad_input = grad_output * (input > 0)
LEAN_EXPORT lean_obj_res scilean_gpu_relu_backward_f32(
    b_lean_obj_arg input_buf,
    b_lean_obj_arg grad_output_buf,
    size_t n,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> input = get_mtl_buffer(input_buf);
    id<MTLBuffer> grad_output = get_mtl_buffer(grad_output_buf);
    if (!input || !grad_output) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"relu_backward");
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get relu_backward pipeline"));
        }

        size_t output_size = n * sizeof(float);
        id<MTLBuffer> grad_input = get_pooled_buffer(output_size);
        if (!grad_input) {
            grad_input = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:input offset:0 atIndex:0];
        [encoder setBuffer:grad_output offset:0 atIndex:1];
        [encoder setBuffer:grad_input offset:0 atIndex:2];

        MTLSize gridSize = MTLSizeMake(n, 1, 1);
        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, n);
        [encoder dispatchThreads:gridSize threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)];

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:grad_input];
        }

        return lean_io_result_mk_ok(wrap_gpu_buffer(grad_input, output_size));
    }
}

// Element-wise multiply backward: grad_a = grad_out * b, grad_b = grad_out * a
// Returns a pair of GpuBuffers (grad_a, grad_b)
LEAN_EXPORT lean_obj_res scilean_gpu_mul_backward_f32(
    b_lean_obj_arg a_buf,
    b_lean_obj_arg b_buf,
    b_lean_obj_arg grad_output_buf,
    size_t n,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> a = get_mtl_buffer(a_buf);
    id<MTLBuffer> b = get_mtl_buffer(b_buf);
    id<MTLBuffer> grad_output = get_mtl_buffer(grad_output_buf);
    if (!a || !b || !grad_output) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"mul_backward");
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get mul_backward pipeline"));
        }

        size_t output_size = n * sizeof(float);
        id<MTLBuffer> grad_a = get_pooled_buffer(output_size);
        id<MTLBuffer> grad_b = get_pooled_buffer(output_size);
        if (!grad_a) grad_a = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        if (!grad_b) grad_b = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];

        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:a offset:0 atIndex:0];
        [encoder setBuffer:b offset:0 atIndex:1];
        [encoder setBuffer:grad_output offset:0 atIndex:2];
        [encoder setBuffer:grad_a offset:0 atIndex:3];
        [encoder setBuffer:grad_b offset:0 atIndex:4];

        MTLSize gridSize = MTLSizeMake(n, 1, 1);
        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, n);
        [encoder dispatchThreads:gridSize threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)];

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:grad_a];
            [g_batch_outputs addObject:grad_b];
        }

        // Return pair as Lean Prod
        lean_obj_res ga = wrap_gpu_buffer(grad_a, output_size);
        lean_obj_res gb = wrap_gpu_buffer(grad_b, output_size);
        lean_obj_res pair = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(pair, 0, ga);
        lean_ctor_set(pair, 1, gb);
        return lean_io_result_mk_ok(pair);
    }
}

// GELU backward
LEAN_EXPORT lean_obj_res scilean_gpu_gelu_backward_f32(
    b_lean_obj_arg input_buf,
    b_lean_obj_arg grad_output_buf,
    size_t n,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> input = get_mtl_buffer(input_buf);
    id<MTLBuffer> grad_output = get_mtl_buffer(grad_output_buf);
    if (!input || !grad_output) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"gelu_backward");
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get gelu_backward pipeline"));
        }

        size_t output_size = n * sizeof(float);
        id<MTLBuffer> grad_input = get_pooled_buffer(output_size);
        if (!grad_input) {
            grad_input = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:input offset:0 atIndex:0];
        [encoder setBuffer:grad_output offset:0 atIndex:1];
        [encoder setBuffer:grad_input offset:0 atIndex:2];

        MTLSize gridSize = MTLSizeMake(n, 1, 1);
        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, n);
        [encoder dispatchThreads:gridSize threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)];

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:grad_input];
        }

        return lean_io_result_mk_ok(wrap_gpu_buffer(grad_input, output_size));
    }
}

// Softmax backward
LEAN_EXPORT lean_obj_res scilean_gpu_softmax_backward_f32(
    b_lean_obj_arg softmax_output_buf,
    b_lean_obj_arg grad_output_buf,
    size_t num_rows,
    size_t row_size,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> softmax_output = get_mtl_buffer(softmax_output_buf);
    id<MTLBuffer> grad_output = get_mtl_buffer(grad_output_buf);
    if (!softmax_output || !grad_output) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"softmax_backward");
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get softmax_backward pipeline"));
        }

        size_t n = num_rows * row_size;
        size_t output_size = n * sizeof(float);
        id<MTLBuffer> grad_input = get_pooled_buffer(output_size);
        if (!grad_input) {
            grad_input = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        uint32_t rows32 = (uint32_t)num_rows;
        uint32_t cols32 = (uint32_t)row_size;

        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:softmax_output offset:0 atIndex:0];
        [encoder setBuffer:grad_output offset:0 atIndex:1];
        [encoder setBuffer:grad_input offset:0 atIndex:2];
        [encoder setBytes:&rows32 length:sizeof(rows32) atIndex:3];
        [encoder setBytes:&cols32 length:sizeof(cols32) atIndex:4];

        MTLSize gridSize = MTLSizeMake(row_size, num_rows, 1);
        NSUInteger tgw = MIN(pipeline.maxTotalThreadsPerThreadgroup, row_size);
        [encoder dispatchThreads:gridSize threadsPerThreadgroup:MTLSizeMake(tgw, 1, 1)];

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:grad_input];
        }

        return lean_io_result_mk_ok(wrap_gpu_buffer(grad_input, output_size));
    }
}

// ============================================================================
// Original FFI Functions (ByteArray-based)
// ============================================================================

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

// Optimized GEMM with shared memory prefetch (Float32)
LEAN_EXPORT lean_obj_res scilean_metal_gemm_simd_opt_f32(
    size_t m, size_t k, size_t n,
    b_lean_obj_arg A,
    b_lean_obj_arg B
) {
    if (!ensure_metal_initialized()) {
        return lean_box(0);
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"gemm_simd_opt");
        if (!pipeline) {
            // Fall back to regular simd if optimized kernel not found
            return scilean_metal_gemm_simd_f32(m, k, n, A, B);
        }

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

        // 8 simdgroups of 32 threads each = 256 threads per threadgroup
        // Each threadgroup computes 64×64 output
        const NSUInteger OPT_TILE_M = 64;
        const NSUInteger OPT_TILE_N = 64;
        MTLSize threadgroupSize = MTLSizeMake(16, 16, 1);  // 256 threads
        MTLSize numThreadgroups = MTLSizeMake(
            (n + OPT_TILE_N - 1) / OPT_TILE_N,
            (m + OPT_TILE_M - 1) / OPT_TILE_M,
            1);

        [encoder dispatchThreadgroups:numThreadgroups threadsPerThreadgroup:threadgroupSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(Cbuf, m * n);
    }
}

// M4-optimized GEMM: simdgroup operations, 64×64 tiles
// REQUIRES: M, N, K are multiples of 64
// Memory: As[64][33] + Bs[32][65] = 16768 bytes (fits 32KB limit)
LEAN_EXPORT lean_obj_res scilean_metal_gemm_m4_f32(
    size_t m, size_t k, size_t n,
    b_lean_obj_arg A,
    b_lean_obj_arg B
) {
    if (!ensure_metal_initialized()) {
        return lean_box(0);
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"gemm_m4");
        if (!pipeline) {
            // Fall back to simd if M4 kernel not available
            return scilean_metal_gemm_simd_f32(m, k, n, A, B);
        }

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

        // 8 simdgroups of 32 threads = 256 threads per threadgroup
        // Each threadgroup computes 64×64 output
        const NSUInteger M4_TILE_M = 64;
        const NSUInteger M4_TILE_N = 64;
        MTLSize threadgroupSize = MTLSizeMake(32, 8, 1);  // 256 threads = 8 simdgroups
        MTLSize numThreadgroups = MTLSizeMake(
            n / M4_TILE_N,  // No rounding - requires aligned size
            m / M4_TILE_M,
            1);

        [encoder dispatchThreadgroups:numThreadgroups threadsPerThreadgroup:threadgroupSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(Cbuf, m * n);
    }
}

// M4-Pro GEMM: Double-buffered with software pipelining
// REQUIRES: M, N, K are multiples of 64
LEAN_EXPORT lean_obj_res scilean_metal_gemm_m4_pro_f32(
    size_t m, size_t k, size_t n,
    b_lean_obj_arg A,
    b_lean_obj_arg B
) {
    if (!ensure_metal_initialized()) {
        return lean_box(0);
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"gemm_m4_pro");
        if (!pipeline) {
            return scilean_metal_gemm_m4_f32(m, k, n, A, B);
        }

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

        const NSUInteger M4P_TILE_M = 64;
        const NSUInteger M4P_TILE_N = 64;
        MTLSize threadgroupSize = MTLSizeMake(32, 8, 1);  // 256 threads = 8 simdgroups
        MTLSize numThreadgroups = MTLSizeMake(
            n / M4P_TILE_N,
            m / M4P_TILE_M,
            1);

        [encoder dispatchThreadgroups:numThreadgroups threadsPerThreadgroup:threadgroupSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(Cbuf, m * n);
    }
}

// M4-Max GEMM: Larger tiles (128×64) for better compute density
// REQUIRES: M multiple of 128, N, K multiples of 64
LEAN_EXPORT lean_obj_res scilean_metal_gemm_m4_max_f32(
    size_t m, size_t k, size_t n,
    b_lean_obj_arg A,
    b_lean_obj_arg B
) {
    if (!ensure_metal_initialized()) {
        return lean_box(0);
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"gemm_m4_max");
        if (!pipeline) {
            return scilean_metal_gemm_m4_f32(m, k, n, A, B);
        }

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

        const NSUInteger M4X_TILE_M = 128;
        const NSUInteger M4X_TILE_N = 64;
        // 512 threads = 16 simdgroups, 32×16 threadgroup layout
        MTLSize threadgroupSize = MTLSizeMake(32, 16, 1);
        MTLSize numThreadgroups = MTLSizeMake(
            n / M4X_TILE_N,
            m / M4X_TILE_M,
            1);

        [encoder dispatchThreadgroups:numThreadgroups threadsPerThreadgroup:threadgroupSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(Cbuf, m * n);
    }
}

// Threshold for CPU fallback: below this, CPU is faster due to GPU dispatch overhead
static const size_t CPU_THRESHOLD_ELEMENTS = 4096;

// Fill (Float32)
// Note: Float32 is passed unboxed (as raw float) in Lean 4.26
LEAN_EXPORT lean_obj_res scilean_metal_fill_f32(size_t n, float value) {
    // CPU fallback for small arrays (avoids ~250µs GPU dispatch overhead)
    if (n <= CPU_THRESHOLD_ELEMENTS) {
        lean_obj_res arr = lean_alloc_sarray(1, n * sizeof(float), n * sizeof(float));
        float* data = (float*)lean_sarray_cptr(arr);
        // Use vDSP for vectorized fill if available
        vDSP_vfill(&value, data, 1, n);
        return arr;
    }

    if (!ensure_metal_initialized()) {
        return lean_box(0);
    }

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

// ============================================================
// CPU-accelerated operations for small arrays (Accelerate/vDSP)
// ============================================================

// Helper: allocate output array and get input/output pointers
static lean_obj_res cpu_unary_alloc(b_lean_obj_arg x, size_t n, const float** in, float** out) {
    lean_obj_res arr = lean_alloc_sarray(1, n * sizeof(float), n * sizeof(float));
    *in = (const float*)lean_sarray_cptr(x);
    *out = (float*)lean_sarray_cptr(arr);
    return arr;
}

// CPU neg: out = -x
static lean_obj_res cpu_neg_f32(size_t n, b_lean_obj_arg x) {
    const float* in; float* out;
    lean_obj_res arr = cpu_unary_alloc(x, n, &in, &out);
    vDSP_vneg(in, 1, out, 1, n);
    return arr;
}

// CPU sqrt: out = sqrt(x)
static lean_obj_res cpu_sqrt_f32(size_t n, b_lean_obj_arg x) {
    const float* in; float* out;
    lean_obj_res arr = cpu_unary_alloc(x, n, &in, &out);
    vvsqrtf(out, in, (const int*)&n);
    return arr;
}

// CPU add: out = a + b
static lean_obj_res cpu_add_f32(size_t n, b_lean_obj_arg a, b_lean_obj_arg b) {
    lean_obj_res arr = lean_alloc_sarray(1, n * sizeof(float), n * sizeof(float));
    const float* ain = (const float*)lean_sarray_cptr(a);
    const float* bin = (const float*)lean_sarray_cptr(b);
    float* out = (float*)lean_sarray_cptr(arr);
    vDSP_vadd(ain, 1, bin, 1, out, 1, n);
    return arr;
}

// CPU sub: out = a - b
static lean_obj_res cpu_sub_f32(size_t n, b_lean_obj_arg a, b_lean_obj_arg b) {
    lean_obj_res arr = lean_alloc_sarray(1, n * sizeof(float), n * sizeof(float));
    const float* ain = (const float*)lean_sarray_cptr(a);
    const float* bin = (const float*)lean_sarray_cptr(b);
    float* out = (float*)lean_sarray_cptr(arr);
    vDSP_vsub(bin, 1, ain, 1, out, 1, n);  // Note: vDSP_vsub is C = A - B but uses (B, A, C) order
    return arr;
}

// CPU mul: out = a * b
static lean_obj_res cpu_mul_f32(size_t n, b_lean_obj_arg a, b_lean_obj_arg b) {
    lean_obj_res arr = lean_alloc_sarray(1, n * sizeof(float), n * sizeof(float));
    const float* ain = (const float*)lean_sarray_cptr(a);
    const float* bin = (const float*)lean_sarray_cptr(b);
    float* out = (float*)lean_sarray_cptr(arr);
    vDSP_vmul(ain, 1, bin, 1, out, 1, n);
    return arr;
}

// CPU div: out = a / b
static lean_obj_res cpu_div_f32(size_t n, b_lean_obj_arg a, b_lean_obj_arg b) {
    lean_obj_res arr = lean_alloc_sarray(1, n * sizeof(float), n * sizeof(float));
    const float* ain = (const float*)lean_sarray_cptr(a);
    const float* bin = (const float*)lean_sarray_cptr(b);
    float* out = (float*)lean_sarray_cptr(arr);
    vDSP_vdiv(bin, 1, ain, 1, out, 1, n);  // Note: vDSP_vdiv is C = A / B but uses (B, A, C) order
    return arr;
}

// CPU reduce sum
static float cpu_reduce_sum_f32(size_t n, b_lean_obj_arg x) {
    const float* in = (const float*)lean_sarray_cptr(x);
    float sum;
    vDSP_sve(in, 1, &sum, n);
    return sum;
}

// CPU reduce max
static float cpu_reduce_max_f32(size_t n, b_lean_obj_arg x) {
    const float* in = (const float*)lean_sarray_cptr(x);
    float maxval;
    vDSP_maxv(in, 1, &maxval, n);
    return maxval;
}

// CPU reduce min
static float cpu_reduce_min_f32(size_t n, b_lean_obj_arg x) {
    const float* in = (const float*)lean_sarray_cptr(x);
    float minval;
    vDSP_minv(in, 1, &minval, n);
    return minval;
}

// ============================================================
// Float32 operations with CPU fallback for small arrays
// ============================================================

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

// Unary op with CPU fallback
#define METAL_UNARY_OP_F32_CPU(name, kernel, cpu_fn) \
LEAN_EXPORT lean_obj_res scilean_metal_##name##_f32(size_t n, b_lean_obj_arg x) { \
    if (n <= CPU_THRESHOLD_ELEMENTS) return cpu_fn(n, x); \
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

// Use CPU fallback for common ops
METAL_UNARY_OP_F32_CPU(neg, "neg", cpu_neg_f32)
METAL_UNARY_OP_F32(exp2, "exp2_op")
METAL_UNARY_OP_F32(log2, "log2_op")
METAL_UNARY_OP_F32(sin, "sin_op")
METAL_UNARY_OP_F32_CPU(sqrt, "sqrt_op", cpu_sqrt_f32)
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

// Binary op with CPU fallback
#define METAL_BINARY_OP_F32_CPU(name, kernel, cpu_fn) \
LEAN_EXPORT lean_obj_res scilean_metal_##name##_f32(size_t n, b_lean_obj_arg a, b_lean_obj_arg b) { \
    if (n <= CPU_THRESHOLD_ELEMENTS) return cpu_fn(n, a, b); \
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

// Use CPU fallback for common binary ops
METAL_BINARY_OP_F32_CPU(add, "add", cpu_add_f32)
METAL_BINARY_OP_F32_CPU(sub, "sub", cpu_sub_f32)
METAL_BINARY_OP_F32_CPU(mul, "mul", cpu_mul_f32)
METAL_BINARY_OP_F32_CPU(div, "div_op", cpu_div_f32)
METAL_BINARY_OP_F32(max, "max_op")
METAL_BINARY_OP_F32(min, "min_op")

// Reduce sum (Float32)
// Note: Returns unboxed float in Lean 4.26
LEAN_EXPORT float scilean_metal_reduce_sum_f32(size_t n, b_lean_obj_arg x) {
    // CPU fallback for small arrays
    if (n <= CPU_THRESHOLD_ELEMENTS) {
        return cpu_reduce_sum_f32(n, x);
    }

    if (!ensure_metal_initialized()) {
        return 0.0f;
    }

    @autoreleasepool {
        id<MTLBuffer> xbuf = create_buffer_from_byte_array_f32(x, n, true);

        // For medium arrays (<=1024 but we already handled small above), use simple single-threadgroup reduction
        if (n <= 1024) {
            id<MTLComputePipelineState> pipeline = get_pipeline(@"reduce_sum");
            if (!pipeline) return 0.0f;

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
            return result[0];
        }

        // For large arrays, use two-pass GPU reduction
        id<MTLComputePipelineState> largePipeline = get_pipeline(@"reduce_sum_large");
        id<MTLComputePipelineState> smallPipeline = get_pipeline(@"reduce_sum");
        if (!largePipeline || !smallPipeline) {
            // Fallback to CPU if kernels unavailable
            float* data = (float*)lean_sarray_cptr(x);
            float sum = 0.0f;
            for (size_t i = 0; i < n; i++) sum += data[i];
            return sum;
        }

        // Pass 1: Reduce to partial sums (one per threadgroup)
        const NSUInteger blockSize = 256;
        NSUInteger numBlocks = MIN(256, (n + blockSize - 1) / blockSize);

        id<MTLBuffer> partialBuf = [device newBufferWithLength:numBlocks * sizeof(float)
                                                       options:MTLResourceStorageModeShared];

        uint32_t n32 = (uint32_t)n;
        uint32_t numBlocks32 = (uint32_t)numBlocks;

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:largePipeline];
        [encoder setBuffer:xbuf offset:0 atIndex:0];
        [encoder setBuffer:partialBuf offset:0 atIndex:1];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:2];
        [encoder setBytes:&numBlocks32 length:sizeof(numBlocks32) atIndex:3];

        MTLSize tgSize = MTLSizeMake(blockSize, 1, 1);
        MTLSize numThreadgroups = MTLSizeMake(numBlocks, 1, 1);
        [encoder dispatchThreadgroups:numThreadgroups threadsPerThreadgroup:tgSize];

        // Pass 2: Reduce partial sums to final result
        id<MTLBuffer> outbuf = [device newBufferWithLength:sizeof(float)
                                                   options:MTLResourceStorageModeShared];

        [encoder setComputePipelineState:smallPipeline];
        [encoder setBuffer:partialBuf offset:0 atIndex:0];
        [encoder setBuffer:outbuf offset:0 atIndex:1];
        [encoder setBytes:&numBlocks32 length:sizeof(numBlocks32) atIndex:2];
        [encoder setThreadgroupMemoryLength:numBlocks * sizeof(float) atIndex:0];

        MTLSize finalGrid = MTLSizeMake(numBlocks, 1, 1);
        MTLSize finalTg = MTLSizeMake(numBlocks, 1, 1);
        [encoder dispatchThreads:finalGrid threadsPerThreadgroup:finalTg];

        [encoder endEncoding];
        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        float* result = (float*)[outbuf contents];
        return result[0];
    }
}

// Reduce max (Float32)
// Note: Returns unboxed float in Lean 4.26
LEAN_EXPORT float scilean_metal_reduce_max_f32(size_t n, b_lean_obj_arg x) {
    // CPU fallback for small arrays
    if (n <= CPU_THRESHOLD_ELEMENTS) {
        return cpu_reduce_max_f32(n, x);
    }

    if (!ensure_metal_initialized()) {
        return -INFINITY;
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"reduce_max");
        if (!pipeline) return -INFINITY;

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
        return result[0];
    }
}

// Reduce min (Float32)
// Note: Returns unboxed float in Lean 4.26
LEAN_EXPORT float scilean_metal_reduce_min_f32(size_t n, b_lean_obj_arg x) {
    // CPU fallback for small arrays
    if (n <= CPU_THRESHOLD_ELEMENTS) {
        return cpu_reduce_min_f32(n, x);
    }

    if (!ensure_metal_initialized()) {
        return INFINITY;
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"reduce_min");
        if (!pipeline) return INFINITY;

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
        return result[0];  // Return raw float, Lean 4.26 expects unboxed Float32
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
    // Get input data - copy to local arrays to ensure correct alignment
    size_t a_elems = m * k;
    size_t b_elems = k * n;
    size_t c_elems = m * n;

    // Allocate aligned temporary buffers for BLAS
    float* aData = (float*)malloc(a_elems * sizeof(float));
    float* bData = (float*)malloc(b_elems * sizeof(float));
    float* cData = (float*)malloc(c_elems * sizeof(float));

    // Copy input data
    memcpy(aData, lean_sarray_cptr(A), a_elems * sizeof(float));
    memcpy(bData, lean_sarray_cptr(B), b_elems * sizeof(float));

    // Initialize C to zero
    memset(cData, 0, c_elems * sizeof(float));

    // Use vDSP for matrix multiply
    // vDSP_mmul: C = A * B
    // A is m×k, B is k×n, C is m×n
    vDSP_mmul(aData, 1, bData, 1, cData, 1, m, n, k);

    // Allocate Lean output and copy result
    size_t c_size = c_elems * sizeof(float);
    lean_obj_res C = lean_alloc_sarray(1, c_size, c_size);
    memcpy(lean_sarray_cptr(C), cData, c_size);

    // Cleanup
    free(aData);
    free(bData);
    free(cData);

    return C;
}

// ============================================================
// Fused ML Operations (Float32)
// ============================================================

// Bias + ReLU: output = max(0, input + bias)
// input: [batch_size, features], bias: [features]
// stride = features (number of bias elements repeated per batch)
LEAN_EXPORT lean_obj_res scilean_metal_bias_relu_f32(
    size_t n,           // total elements
    size_t stride,      // bias stride (features per sample)
    b_lean_obj_arg input,
    b_lean_obj_arg bias
) {
    if (!ensure_metal_initialized()) {
        return lean_box(0);
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"bias_relu");
        if (!pipeline) return lean_box(0);

        id<MTLBuffer> inputBuf = create_buffer_from_byte_array_f32(input, n, true);
        id<MTLBuffer> biasBuf = create_buffer_from_byte_array_f32(bias, stride, true);
        id<MTLBuffer> outputBuf = [device newBufferWithLength:n * sizeof(float)
                                                      options:MTLResourceStorageModeShared];

        uint32_t n32 = (uint32_t)n;
        uint32_t stride32 = (uint32_t)stride;

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:inputBuf offset:0 atIndex:0];
        [encoder setBuffer:biasBuf offset:0 atIndex:1];
        [encoder setBuffer:outputBuf offset:0 atIndex:2];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:3];
        [encoder setBytes:&stride32 length:sizeof(stride32) atIndex:4];

        MTLSize gridSize = MTLSizeMake(n, 1, 1);
        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, n);
        [encoder dispatchThreads:gridSize threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(outputBuf, n);
    }
}

// Bias + GELU: output = input * 0.5 * (1 + tanh(sqrt(2/π) * (input + 0.044715 * input³)))
LEAN_EXPORT lean_obj_res scilean_metal_bias_gelu_f32(
    size_t n,
    size_t stride,
    b_lean_obj_arg input,
    b_lean_obj_arg bias
) {
    if (!ensure_metal_initialized()) {
        return lean_box(0);
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"bias_gelu");
        if (!pipeline) return lean_box(0);

        id<MTLBuffer> inputBuf = create_buffer_from_byte_array_f32(input, n, true);
        id<MTLBuffer> biasBuf = create_buffer_from_byte_array_f32(bias, stride, true);
        id<MTLBuffer> outputBuf = [device newBufferWithLength:n * sizeof(float)
                                                      options:MTLResourceStorageModeShared];

        uint32_t n32 = (uint32_t)n;
        uint32_t stride32 = (uint32_t)stride;

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:inputBuf offset:0 atIndex:0];
        [encoder setBuffer:biasBuf offset:0 atIndex:1];
        [encoder setBuffer:outputBuf offset:0 atIndex:2];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:3];
        [encoder setBytes:&stride32 length:sizeof(stride32) atIndex:4];

        MTLSize gridSize = MTLSizeMake(n, 1, 1);
        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, n);
        [encoder dispatchThreads:gridSize threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(outputBuf, n);
    }
}

// Layer Norm: output = gamma * (input - mean) / sqrt(var + eps) + beta
// Simplified version: each sample normalized independently
// n = total elements, hiddenSize = features per sample
LEAN_EXPORT lean_obj_res scilean_metal_layer_norm_f32(
    size_t n,
    size_t hiddenSize,
    b_lean_obj_arg input,
    b_lean_obj_arg gamma,
    b_lean_obj_arg beta
) {
    if (!ensure_metal_initialized()) {
        return lean_box(0);
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"layer_norm");
        if (!pipeline) return lean_box(0);

        id<MTLBuffer> inputBuf = create_buffer_from_byte_array_f32(input, n, true);
        id<MTLBuffer> gammaBuf = create_buffer_from_byte_array_f32(gamma, hiddenSize, true);
        id<MTLBuffer> betaBuf = create_buffer_from_byte_array_f32(beta, hiddenSize, true);
        id<MTLBuffer> outputBuf = [device newBufferWithLength:n * sizeof(float)
                                                      options:MTLResourceStorageModeShared];

        uint32_t n32 = (uint32_t)n;
        uint32_t hiddenSize32 = (uint32_t)hiddenSize;
        float eps = 1e-5f;

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:inputBuf offset:0 atIndex:0];
        [encoder setBuffer:gammaBuf offset:0 atIndex:1];
        [encoder setBuffer:betaBuf offset:0 atIndex:2];
        [encoder setBuffer:outputBuf offset:0 atIndex:3];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:4];
        [encoder setBytes:&hiddenSize32 length:sizeof(hiddenSize32) atIndex:5];
        [encoder setBytes:&eps length:sizeof(eps) atIndex:6];

        MTLSize gridSize = MTLSizeMake(n, 1, 1);
        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, n);
        [encoder dispatchThreads:gridSize threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(outputBuf, n);
    }
}

// ============================================================
// Attention Operations (Float32)
// ============================================================

// Flash Attention - single head
// Q, K, V: [seq_len, head_dim]
// output: [seq_len, head_dim]
LEAN_EXPORT lean_obj_res scilean_metal_flash_attention_f32(
    size_t seq_len,
    size_t head_dim,
    b_lean_obj_arg q_arr,
    b_lean_obj_arg k_arr,
    b_lean_obj_arg v_arr
) {
    if (!ensure_metal_initialized()) {
        return empty_byte_array_f32();
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"flash_attention");
        if (!pipeline) {
            NSLog(@"Flash attention: Failed to get pipeline");
            return empty_byte_array_f32();
        }

        size_t n = seq_len * head_dim;
        id<MTLBuffer> qBuf = create_buffer_from_byte_array_f32(q_arr, n, true);
        id<MTLBuffer> kBuf = create_buffer_from_byte_array_f32(k_arr, n, true);
        id<MTLBuffer> vBuf = create_buffer_from_byte_array_f32(v_arr, n, true);
        id<MTLBuffer> outputBuf = [device newBufferWithLength:n * sizeof(float)
                                                      options:MTLResourceStorageModeShared];

        uint32_t seq_len32 = (uint32_t)seq_len;
        uint32_t head_dim32 = (uint32_t)head_dim;
        float scale = 1.0f / sqrtf((float)head_dim);

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:qBuf offset:0 atIndex:0];
        [encoder setBuffer:kBuf offset:0 atIndex:1];
        [encoder setBuffer:vBuf offset:0 atIndex:2];
        [encoder setBuffer:outputBuf offset:0 atIndex:3];
        [encoder setBytes:&seq_len32 length:sizeof(seq_len32) atIndex:4];
        [encoder setBytes:&head_dim32 length:sizeof(head_dim32) atIndex:5];
        [encoder setBytes:&scale length:sizeof(scale) atIndex:6];

        // Simple serial kernel: one thread per query position
        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, 256);
        [encoder dispatchThreads:MTLSizeMake(seq_len, 1, 1)
           threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(outputBuf, n);
    }
}

// Flash Attention - causal (autoregressive) variant
// Only attends to positions <= current position
LEAN_EXPORT lean_obj_res scilean_metal_flash_attention_causal_f32(
    size_t seq_len,
    size_t head_dim,
    b_lean_obj_arg q_arr,
    b_lean_obj_arg k_arr,
    b_lean_obj_arg v_arr
) {
    if (!ensure_metal_initialized()) {
        return empty_byte_array_f32();
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"flash_attention_causal");
        if (!pipeline) {
            NSLog(@"Flash attention causal: Failed to get pipeline");
            return empty_byte_array_f32();
        }

        size_t n = seq_len * head_dim;
        id<MTLBuffer> qBuf = create_buffer_from_byte_array_f32(q_arr, n, true);
        id<MTLBuffer> kBuf = create_buffer_from_byte_array_f32(k_arr, n, true);
        id<MTLBuffer> vBuf = create_buffer_from_byte_array_f32(v_arr, n, true);
        id<MTLBuffer> outputBuf = [device newBufferWithLength:n * sizeof(float)
                                                      options:MTLResourceStorageModeShared];

        uint32_t seq_len32 = (uint32_t)seq_len;
        uint32_t head_dim32 = (uint32_t)head_dim;
        float scale = 1.0f / sqrtf((float)head_dim);

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:qBuf offset:0 atIndex:0];
        [encoder setBuffer:kBuf offset:0 atIndex:1];
        [encoder setBuffer:vBuf offset:0 atIndex:2];
        [encoder setBuffer:outputBuf offset:0 atIndex:3];
        [encoder setBytes:&seq_len32 length:sizeof(seq_len32) atIndex:4];
        [encoder setBytes:&head_dim32 length:sizeof(head_dim32) atIndex:5];
        [encoder setBytes:&scale length:sizeof(scale) atIndex:6];

        // Simple serial kernel: one thread per query position
        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, 256);
        [encoder dispatchThreads:MTLSizeMake(seq_len, 1, 1)
           threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(outputBuf, n);
    }
}

// Multi-head attention
// Q, K, V: [batch, num_heads, seq_len, head_dim]
// output: [batch, num_heads, seq_len, head_dim]
LEAN_EXPORT lean_obj_res scilean_metal_attention_multihead_f32(
    size_t batch_size,
    size_t num_heads,
    size_t seq_len,
    size_t head_dim,
    b_lean_obj_arg q_arr,
    b_lean_obj_arg k_arr,
    b_lean_obj_arg v_arr
) {
    if (!ensure_metal_initialized()) {
        return empty_byte_array_f32();
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"attention_multi_head");
        if (!pipeline) {
            NSLog(@"Multi-head attention: Failed to get pipeline");
            return empty_byte_array_f32();
        }

        size_t n = batch_size * num_heads * seq_len * head_dim;
        id<MTLBuffer> qBuf = create_buffer_from_byte_array_f32(q_arr, n, true);
        id<MTLBuffer> kBuf = create_buffer_from_byte_array_f32(k_arr, n, true);
        id<MTLBuffer> vBuf = create_buffer_from_byte_array_f32(v_arr, n, true);
        id<MTLBuffer> outputBuf = [device newBufferWithLength:n * sizeof(float)
                                                      options:MTLResourceStorageModeShared];

        uint32_t batch_size32 = (uint32_t)batch_size;
        uint32_t num_heads32 = (uint32_t)num_heads;
        uint32_t seq_len32 = (uint32_t)seq_len;
        uint32_t head_dim32 = (uint32_t)head_dim;
        float scale = 1.0f / sqrtf((float)head_dim);

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:qBuf offset:0 atIndex:0];
        [encoder setBuffer:kBuf offset:0 atIndex:1];
        [encoder setBuffer:vBuf offset:0 atIndex:2];
        [encoder setBuffer:outputBuf offset:0 atIndex:3];
        [encoder setBytes:&batch_size32 length:sizeof(batch_size32) atIndex:4];
        [encoder setBytes:&num_heads32 length:sizeof(num_heads32) atIndex:5];
        [encoder setBytes:&seq_len32 length:sizeof(seq_len32) atIndex:6];
        [encoder setBytes:&head_dim32 length:sizeof(head_dim32) atIndex:7];
        [encoder setBytes:&scale length:sizeof(scale) atIndex:8];

        // Grid: (num_heads, batch_size, ceil(seq_len/threads))
        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, 256);
        NSUInteger q_tiles = (seq_len + tgSize - 1) / tgSize;
        [encoder dispatchThreadgroups:MTLSizeMake(num_heads, batch_size, q_tiles)
                threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(outputBuf, n);
    }
}

// Batched softmax (row-wise) - commonly used in attention
// Input: [num_rows, row_size], applies softmax to each row
LEAN_EXPORT lean_obj_res scilean_metal_softmax_batched_f32(
    size_t num_rows,
    size_t row_size,
    b_lean_obj_arg x
) {
    if (!ensure_metal_initialized()) {
        return empty_byte_array_f32();
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"softmax_batched");
        if (!pipeline) {
            NSLog(@"Softmax batched: Failed to get pipeline");
            return empty_byte_array_f32();
        }

        size_t n = num_rows * row_size;
        id<MTLBuffer> inputBuf = create_buffer_from_byte_array_f32(x, n, true);
        id<MTLBuffer> outputBuf = [device newBufferWithLength:n * sizeof(float)
                                                      options:MTLResourceStorageModeShared];

        uint32_t row_size32 = (uint32_t)row_size;

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:inputBuf offset:0 atIndex:0];
        [encoder setBuffer:outputBuf offset:0 atIndex:1];
        [encoder setBytes:&row_size32 length:sizeof(row_size32) atIndex:2];

        // Shared memory for row data
        [encoder setThreadgroupMemoryLength:row_size * sizeof(float) atIndex:0];

        // One threadgroup per row
        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, 256);
        [encoder dispatchThreadgroups:MTLSizeMake(num_rows, 1, 1)
                threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(outputBuf, n);
    }
}

// ============================================================================
// Conv2D operations
// ============================================================================

// Conv2D with optional ReLU
// Input: NCHW format [batch, in_channels, height, width]
// Kernel: OIHW format [out_channels, in_channels, kernel_h, kernel_w]
// Bias: [out_channels]
// Output: NCHW format
LEAN_EXPORT lean_obj_res scilean_metal_conv2d_f32(
    size_t batch_size,
    size_t in_channels,
    size_t out_channels,
    size_t in_height,
    size_t in_width,
    size_t kernel_h,
    size_t kernel_w,
    size_t stride_h,
    size_t stride_w,
    size_t pad_h,
    size_t pad_w,
    uint8_t use_relu,
    b_lean_obj_arg input_arr,
    b_lean_obj_arg kernel_arr,
    b_lean_obj_arg bias_arr
) {
    if (!ensure_metal_initialized()) {
        return empty_byte_array_f32();
    }

    @autoreleasepool {
        const char* kernel_name = use_relu ? "conv2d_relu" : "conv2d_naive";
        id<MTLComputePipelineState> pipeline = get_pipeline([NSString stringWithUTF8String:kernel_name]);
        if (!pipeline) {
            NSLog(@"Conv2D: Failed to get pipeline for %s", kernel_name);
            return empty_byte_array_f32();
        }

        // Output dimensions
        size_t out_height = (in_height + 2 * pad_h - kernel_h) / stride_h + 1;
        size_t out_width = (in_width + 2 * pad_w - kernel_w) / stride_w + 1;

        size_t input_size = batch_size * in_channels * in_height * in_width;
        size_t kernel_size = out_channels * in_channels * kernel_h * kernel_w;
        size_t output_size = batch_size * out_channels * out_height * out_width;

        id<MTLBuffer> inputBuf = create_buffer_from_byte_array_f32(input_arr, input_size, true);
        id<MTLBuffer> kernelBuf = create_buffer_from_byte_array_f32(kernel_arr, kernel_size, true);
        id<MTLBuffer> biasBuf = create_buffer_from_byte_array_f32(bias_arr, out_channels, true);
        id<MTLBuffer> outputBuf = [device newBufferWithLength:output_size * sizeof(float)
                                                      options:MTLResourceStorageModeShared];

        uint32_t batch32 = (uint32_t)batch_size;
        uint32_t ic32 = (uint32_t)in_channels;
        uint32_t oc32 = (uint32_t)out_channels;
        uint32_t ih32 = (uint32_t)in_height;
        uint32_t iw32 = (uint32_t)in_width;
        uint32_t kh32 = (uint32_t)kernel_h;
        uint32_t kw32 = (uint32_t)kernel_w;
        uint32_t sh32 = (uint32_t)stride_h;
        uint32_t sw32 = (uint32_t)stride_w;
        uint32_t ph32 = (uint32_t)pad_h;
        uint32_t pw32 = (uint32_t)pad_w;

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:inputBuf offset:0 atIndex:0];
        [encoder setBuffer:kernelBuf offset:0 atIndex:1];
        [encoder setBuffer:biasBuf offset:0 atIndex:2];
        [encoder setBuffer:outputBuf offset:0 atIndex:3];
        [encoder setBytes:&batch32 length:sizeof(batch32) atIndex:4];
        [encoder setBytes:&ic32 length:sizeof(ic32) atIndex:5];
        [encoder setBytes:&oc32 length:sizeof(oc32) atIndex:6];
        [encoder setBytes:&ih32 length:sizeof(ih32) atIndex:7];
        [encoder setBytes:&iw32 length:sizeof(iw32) atIndex:8];
        [encoder setBytes:&kh32 length:sizeof(kh32) atIndex:9];
        [encoder setBytes:&kw32 length:sizeof(kw32) atIndex:10];
        [encoder setBytes:&sh32 length:sizeof(sh32) atIndex:11];
        [encoder setBytes:&sw32 length:sizeof(sw32) atIndex:12];
        [encoder setBytes:&ph32 length:sizeof(ph32) atIndex:13];
        [encoder setBytes:&pw32 length:sizeof(pw32) atIndex:14];

        // Grid: (out_width, out_height, batch * out_channels)
        MTLSize gridSize = MTLSizeMake(out_width, out_height, batch_size * out_channels);
        NSUInteger w = MIN(pipeline.maxTotalThreadsPerThreadgroup, 16);
        MTLSize tgSize = MTLSizeMake(w, w, 1);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:tgSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(outputBuf, output_size);
    }
}

// Conv2D optimized using simdgroup matrix operations
// Uses the conv2d_3x3_winograd kernel for 3x3 convolutions with stride 1
LEAN_EXPORT lean_obj_res scilean_metal_conv2d_fast_f32(
    size_t batch_size,
    size_t in_channels,
    size_t out_channels,
    size_t in_height,
    size_t in_width,
    size_t kernel_h,
    size_t kernel_w,
    size_t stride_h,
    size_t stride_w,
    size_t pad_h,
    size_t pad_w,
    uint8_t use_relu,
    b_lean_obj_arg input_arr,
    b_lean_obj_arg kernel_arr,
    b_lean_obj_arg bias_arr
) {
    if (!ensure_metal_initialized()) {
        return empty_byte_array_f32();
    }

    @autoreleasepool {
        // Use specialized 3x3 kernel for 3x3 convolutions with stride 1 and padding 1
        bool use_3x3 = (kernel_h == 3 && kernel_w == 3 &&
                        stride_h == 1 && stride_w == 1 &&
                        pad_h == 1 && pad_w == 1);

        const char* kernel_name = use_3x3 ? "conv2d_3x3_winograd" : (use_relu ? "conv2d_relu" : "conv2d_naive");
        id<MTLComputePipelineState> pipeline = get_pipeline([NSString stringWithUTF8String:kernel_name]);
        if (!pipeline) {
            NSLog(@"Conv2D Fast: Failed to get pipeline for %s", kernel_name);
            return empty_byte_array_f32();
        }

        // Output dimensions
        size_t out_height = (in_height + 2 * pad_h - kernel_h) / stride_h + 1;
        size_t out_width = (in_width + 2 * pad_w - kernel_w) / stride_w + 1;

        size_t input_size = batch_size * in_channels * in_height * in_width;
        size_t kernel_size = out_channels * in_channels * kernel_h * kernel_w;
        size_t output_size = batch_size * out_channels * out_height * out_width;

        id<MTLBuffer> inputBuf = create_buffer_from_byte_array_f32(input_arr, input_size, true);
        id<MTLBuffer> kernelBuf = create_buffer_from_byte_array_f32(kernel_arr, kernel_size, true);
        id<MTLBuffer> biasBuf = create_buffer_from_byte_array_f32(bias_arr, out_channels, true);
        id<MTLBuffer> outputBuf = [device newBufferWithLength:output_size * sizeof(float)
                                                      options:MTLResourceStorageModeShared];

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:inputBuf offset:0 atIndex:0];
        [encoder setBuffer:kernelBuf offset:0 atIndex:1];
        [encoder setBuffer:biasBuf offset:0 atIndex:2];
        [encoder setBuffer:outputBuf offset:0 atIndex:3];

        if (use_3x3) {
            // 3x3 optimized kernel has fewer parameters
            uint32_t batch32 = (uint32_t)batch_size;
            uint32_t ic32 = (uint32_t)in_channels;
            uint32_t oc32 = (uint32_t)out_channels;
            uint32_t ih32 = (uint32_t)in_height;
            uint32_t iw32 = (uint32_t)in_width;
            uint32_t relu32 = (uint32_t)use_relu;

            [encoder setBytes:&batch32 length:sizeof(batch32) atIndex:4];
            [encoder setBytes:&ic32 length:sizeof(ic32) atIndex:5];
            [encoder setBytes:&oc32 length:sizeof(oc32) atIndex:6];
            [encoder setBytes:&ih32 length:sizeof(ih32) atIndex:7];
            [encoder setBytes:&iw32 length:sizeof(iw32) atIndex:8];
            [encoder setBytes:&relu32 length:sizeof(relu32) atIndex:9];
        } else {
            uint32_t batch32 = (uint32_t)batch_size;
            uint32_t ic32 = (uint32_t)in_channels;
            uint32_t oc32 = (uint32_t)out_channels;
            uint32_t ih32 = (uint32_t)in_height;
            uint32_t iw32 = (uint32_t)in_width;
            uint32_t kh32 = (uint32_t)kernel_h;
            uint32_t kw32 = (uint32_t)kernel_w;
            uint32_t sh32 = (uint32_t)stride_h;
            uint32_t sw32 = (uint32_t)stride_w;
            uint32_t ph32 = (uint32_t)pad_h;
            uint32_t pw32 = (uint32_t)pad_w;

            [encoder setBytes:&batch32 length:sizeof(batch32) atIndex:4];
            [encoder setBytes:&ic32 length:sizeof(ic32) atIndex:5];
            [encoder setBytes:&oc32 length:sizeof(oc32) atIndex:6];
            [encoder setBytes:&ih32 length:sizeof(ih32) atIndex:7];
            [encoder setBytes:&iw32 length:sizeof(iw32) atIndex:8];
            [encoder setBytes:&kh32 length:sizeof(kh32) atIndex:9];
            [encoder setBytes:&kw32 length:sizeof(kw32) atIndex:10];
            [encoder setBytes:&sh32 length:sizeof(sh32) atIndex:11];
            [encoder setBytes:&sw32 length:sizeof(sw32) atIndex:12];
            [encoder setBytes:&ph32 length:sizeof(ph32) atIndex:13];
            [encoder setBytes:&pw32 length:sizeof(pw32) atIndex:14];
        }

        // Grid: (out_width, out_height, batch * out_channels)
        MTLSize gridSize = MTLSizeMake(out_width, out_height, batch_size * out_channels);
        NSUInteger w = MIN(pipeline.maxTotalThreadsPerThreadgroup, 16);
        MTLSize tgSize = MTLSizeMake(w, w, 1);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:tgSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(outputBuf, output_size);
    }
}

// Conv2D using im2col + GEMM approach
// This converts convolution to matrix multiplication which can use highly optimized GEMM
// im2col creates a [K, N] matrix, then output = weights[M,K] * im2col[K,N]
LEAN_EXPORT lean_obj_res scilean_metal_conv2d_gemm_f32(
    size_t batch_size,
    size_t in_channels,
    size_t out_channels,
    size_t in_height,
    size_t in_width,
    size_t kernel_h,
    size_t kernel_w,
    size_t stride_h,
    size_t stride_w,
    size_t pad_h,
    size_t pad_w,
    uint8_t use_relu,
    b_lean_obj_arg input_arr,
    b_lean_obj_arg kernel_arr,
    b_lean_obj_arg bias_arr
) {
    if (!ensure_metal_initialized()) {
        return empty_byte_array_f32();
    }

    @autoreleasepool {
        // Output dimensions
        size_t out_height = (in_height + 2 * pad_h - kernel_h) / stride_h + 1;
        size_t out_width = (in_width + 2 * pad_w - kernel_w) / stride_w + 1;

        // GEMM dimensions
        size_t M = out_channels;                           // Output rows
        size_t K = in_channels * kernel_h * kernel_w;     // Reduction dimension
        size_t N = out_height * out_width;                 // Output columns (spatial)

        size_t input_size = batch_size * in_channels * in_height * in_width;
        size_t output_size = batch_size * out_channels * out_height * out_width;
        size_t im2col_size = K * N;

        // Create buffers
        id<MTLBuffer> inputBuf = create_buffer_from_byte_array_f32(input_arr, input_size, true);
        id<MTLBuffer> weightsBuf = create_buffer_from_byte_array_f32(kernel_arr, M * K, true);
        id<MTLBuffer> biasBuf = create_buffer_from_byte_array_f32(bias_arr, out_channels, true);
        id<MTLBuffer> im2colBuf = [device newBufferWithLength:im2col_size * sizeof(float)
                                                      options:MTLResourceStorageModeShared];
        id<MTLBuffer> outputBuf = [device newBufferWithLength:output_size * sizeof(float)
                                                      options:MTLResourceStorageModeShared];

        // Get pipelines
        id<MTLComputePipelineState> im2colPipeline = get_pipeline(@"conv2d_im2col");
        id<MTLComputePipelineState> gemmPipeline = get_pipeline(@"gemm_simd");

        if (!im2colPipeline || !gemmPipeline) {
            NSLog(@"Conv2D GEMM: Failed to get pipelines");
            return empty_byte_array_f32();
        }

        for (size_t b = 0; b < batch_size; b++) {
            // Step 1: im2col transformation for this batch
            id<MTLCommandBuffer> im2colCmd = [commandQueue commandBuffer];
            id<MTLComputeCommandEncoder> im2colEnc = [im2colCmd computeCommandEncoder];

            [im2colEnc setComputePipelineState:im2colPipeline];
            [im2colEnc setBuffer:inputBuf offset:b * in_channels * in_height * in_width * sizeof(float) atIndex:0];
            [im2colEnc setBuffer:im2colBuf offset:0 atIndex:1];

            uint32_t batch32 = (uint32_t)b;
            uint32_t ic32 = (uint32_t)in_channels;
            uint32_t ih32 = (uint32_t)in_height;
            uint32_t iw32 = (uint32_t)in_width;
            uint32_t kh32 = (uint32_t)kernel_h;
            uint32_t kw32 = (uint32_t)kernel_w;
            uint32_t sh32 = (uint32_t)stride_h;
            uint32_t sw32 = (uint32_t)stride_w;
            uint32_t ph32 = (uint32_t)pad_h;
            uint32_t pw32 = (uint32_t)pad_w;
            uint32_t oh32 = (uint32_t)out_height;
            uint32_t ow32 = (uint32_t)out_width;

            [im2colEnc setBytes:&batch32 length:sizeof(batch32) atIndex:2];
            [im2colEnc setBytes:&ic32 length:sizeof(ic32) atIndex:3];
            [im2colEnc setBytes:&ih32 length:sizeof(ih32) atIndex:4];
            [im2colEnc setBytes:&iw32 length:sizeof(iw32) atIndex:5];
            [im2colEnc setBytes:&kh32 length:sizeof(kh32) atIndex:6];
            [im2colEnc setBytes:&kw32 length:sizeof(kw32) atIndex:7];
            [im2colEnc setBytes:&sh32 length:sizeof(sh32) atIndex:8];
            [im2colEnc setBytes:&sw32 length:sizeof(sw32) atIndex:9];
            [im2colEnc setBytes:&ph32 length:sizeof(ph32) atIndex:10];
            [im2colEnc setBytes:&pw32 length:sizeof(pw32) atIndex:11];
            [im2colEnc setBytes:&oh32 length:sizeof(oh32) atIndex:12];
            [im2colEnc setBytes:&ow32 length:sizeof(ow32) atIndex:13];

            // Grid: [N, K] where N = out_spatial, K = in_channels * kernel_h * kernel_w
            MTLSize im2colGrid = MTLSizeMake(N, K, 1);
            MTLSize im2colTG = MTLSizeMake(16, 16, 1);

            [im2colEnc dispatchThreads:im2colGrid threadsPerThreadgroup:im2colTG];
            [im2colEnc endEncoding];
            [im2colCmd commit];
            [im2colCmd waitUntilCompleted];

            // Step 2: GEMM: output[M,N] = weights[M,K] * im2col[K,N]
            id<MTLCommandBuffer> gemmCmd = [commandQueue commandBuffer];
            id<MTLComputeCommandEncoder> gemmEnc = [gemmCmd computeCommandEncoder];

            [gemmEnc setComputePipelineState:gemmPipeline];
            [gemmEnc setBuffer:weightsBuf offset:0 atIndex:0];     // A = weights [M, K]
            [gemmEnc setBuffer:im2colBuf offset:0 atIndex:1];       // B = im2col [K, N]
            [gemmEnc setBuffer:outputBuf offset:b * M * N * sizeof(float) atIndex:2];  // C = output [M, N]

            uint32_t M32 = (uint32_t)M;
            uint32_t K32 = (uint32_t)K;
            uint32_t N32 = (uint32_t)N;
            [gemmEnc setBytes:&M32 length:sizeof(M32) atIndex:3];
            [gemmEnc setBytes:&K32 length:sizeof(K32) atIndex:4];
            [gemmEnc setBytes:&N32 length:sizeof(N32) atIndex:5];

            // Use 32x32 tiles, 4 simdgroups
            MTLSize gemmGrid = MTLSizeMake((N + 31) / 32, (M + 31) / 32, 1);
            MTLSize gemmTG = MTLSizeMake(32, 4, 1);

            [gemmEnc dispatchThreadgroups:gemmGrid threadsPerThreadgroup:gemmTG];
            [gemmEnc endEncoding];
            [gemmCmd commit];
            [gemmCmd waitUntilCompleted];
        }

        // Add bias (and optionally ReLU)
        float* output_ptr = (float*)outputBuf.contents;
        const float* bias_ptr = (const float*)lean_sarray_cptr(bias_arr);

        for (size_t b = 0; b < batch_size; b++) {
            for (size_t oc = 0; oc < out_channels; oc++) {
                float bias_val = bias_ptr[oc];
                for (size_t spatial = 0; spatial < N; spatial++) {
                    size_t idx = b * out_channels * N + oc * N + spatial;
                    float val = output_ptr[idx] + bias_val;
                    if (use_relu && val < 0) val = 0;
                    output_ptr[idx] = val;
                }
            }
        }

        return buffer_to_byte_array_f32(outputBuf, output_size);
    }
}

// Conv2D using Metal Performance Shaders (MPS) for maximum performance
// MPS convolution is highly optimized by Apple and typically much faster than custom kernels
LEAN_EXPORT lean_obj_res scilean_metal_conv2d_mps_f32(
    size_t batch_size,
    size_t in_channels,
    size_t out_channels,
    size_t in_height,
    size_t in_width,
    size_t kernel_h,
    size_t kernel_w,
    size_t stride_h,
    size_t stride_w,
    size_t pad_h,
    size_t pad_w,
    uint8_t use_relu,
    b_lean_obj_arg input_arr,
    b_lean_obj_arg kernel_arr,
    b_lean_obj_arg bias_arr
) {
    if (!ensure_metal_initialized()) {
        return empty_byte_array_f32();
    }

    @autoreleasepool {
        // Create MPS convolution descriptor
        MPSCNNConvolutionDescriptor *convDesc = [MPSCNNConvolutionDescriptor
            cnnConvolutionDescriptorWithKernelWidth:kernel_w
            kernelHeight:kernel_h
            inputFeatureChannels:in_channels
            outputFeatureChannels:out_channels];

        convDesc.strideInPixelsX = stride_w;
        convDesc.strideInPixelsY = stride_h;

        // Create weight data source
        // MPS expects weights in OIHW format (same as our format)
        size_t weight_size = out_channels * in_channels * kernel_h * kernel_w;
        float* weights_ptr = (float*)malloc(weight_size * sizeof(float));
        memcpy(weights_ptr, lean_sarray_cptr(kernel_arr), weight_size * sizeof(float));

        // Bias data
        float* bias_ptr = (float*)malloc(out_channels * sizeof(float));
        memcpy(bias_ptr, lean_sarray_cptr(bias_arr), out_channels * sizeof(float));

        // Create convolution data source
        // Note: For simplicity, we'll use the basic MPSCNNConvolution which takes pre-loaded weights
        // For production, use MPSCNNConvolutionDataSource protocol for better memory management

        // Create MPS image descriptors
        // Note: MPS uses NCHW format (batch, channels, height, width) which matches our format
        MPSImageDescriptor *inputDesc = [MPSImageDescriptor
            imageDescriptorWithChannelFormat:MPSImageFeatureChannelFormatFloat32
            width:in_width
            height:in_height
            featureChannels:in_channels
            numberOfImages:batch_size
            usage:MTLTextureUsageShaderRead];

        size_t out_height = (in_height + 2 * pad_h - kernel_h) / stride_h + 1;
        size_t out_width = (in_width + 2 * pad_w - kernel_w) / stride_w + 1;

        MPSImageDescriptor *outputDesc = [MPSImageDescriptor
            imageDescriptorWithChannelFormat:MPSImageFeatureChannelFormatFloat32
            width:out_width
            height:out_height
            featureChannels:out_channels
            numberOfImages:batch_size
            usage:MTLTextureUsageShaderWrite];

        // Create input/output images
        MPSImage *inputImage = [[MPSImage alloc] initWithDevice:device imageDescriptor:inputDesc];
        MPSImage *outputImage = [[MPSImage alloc] initWithDevice:device imageDescriptor:outputDesc];

        // Copy input data to MPS image
        size_t input_size = batch_size * in_channels * in_height * in_width;
        const float* input_data = (const float*)lean_sarray_cptr(input_arr);

        // MPS images use a specific memory layout - need to use writeBytes
        MTLRegion region = MTLRegionMake3D(0, 0, 0, in_width, in_height, in_channels);
        size_t bytesPerRow = in_width * sizeof(float);
        size_t bytesPerImage = in_height * bytesPerRow;
        [inputImage.texture replaceRegion:region
                             mipmapLevel:0
                                   slice:0
                               withBytes:input_data
                             bytesPerRow:bytesPerRow
                           bytesPerImage:bytesPerImage];

        // For now, fall back to our custom kernel since MPS setup is complex
        // The MPS CNN APIs require careful data layout and weight management
        free(weights_ptr);
        free(bias_ptr);

        // Use our fast kernel as a fallback
        return scilean_metal_conv2d_fast_f32(batch_size, in_channels, out_channels,
                                              in_height, in_width, kernel_h, kernel_w,
                                              stride_h, stride_w, pad_h, pad_w, use_relu,
                                              input_arr, kernel_arr, bias_arr);
    }
}

// MaxPool2D
LEAN_EXPORT lean_obj_res scilean_metal_maxpool2d_f32(
    size_t batch_size,
    size_t channels,
    size_t in_height,
    size_t in_width,
    size_t pool_h,
    size_t pool_w,
    size_t stride_h,
    size_t stride_w,
    b_lean_obj_arg input_arr
) {
    if (!ensure_metal_initialized()) {
        return empty_byte_array_f32();
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"maxpool2d");
        if (!pipeline) {
            NSLog(@"MaxPool2D: Failed to get pipeline");
            return empty_byte_array_f32();
        }

        size_t out_height = (in_height - pool_h) / stride_h + 1;
        size_t out_width = (in_width - pool_w) / stride_w + 1;

        size_t input_size = batch_size * channels * in_height * in_width;
        size_t output_size = batch_size * channels * out_height * out_width;

        id<MTLBuffer> inputBuf = create_buffer_from_byte_array_f32(input_arr, input_size, true);
        id<MTLBuffer> outputBuf = [device newBufferWithLength:output_size * sizeof(float)
                                                      options:MTLResourceStorageModeShared];

        uint32_t batch32 = (uint32_t)batch_size;
        uint32_t c32 = (uint32_t)channels;
        uint32_t ih32 = (uint32_t)in_height;
        uint32_t iw32 = (uint32_t)in_width;
        uint32_t ph32 = (uint32_t)pool_h;
        uint32_t pw32 = (uint32_t)pool_w;
        uint32_t sh32 = (uint32_t)stride_h;
        uint32_t sw32 = (uint32_t)stride_w;

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:inputBuf offset:0 atIndex:0];
        [encoder setBuffer:outputBuf offset:0 atIndex:1];
        [encoder setBytes:&batch32 length:sizeof(batch32) atIndex:2];
        [encoder setBytes:&c32 length:sizeof(c32) atIndex:3];
        [encoder setBytes:&ih32 length:sizeof(ih32) atIndex:4];
        [encoder setBytes:&iw32 length:sizeof(iw32) atIndex:5];
        [encoder setBytes:&ph32 length:sizeof(ph32) atIndex:6];
        [encoder setBytes:&pw32 length:sizeof(pw32) atIndex:7];
        [encoder setBytes:&sh32 length:sizeof(sh32) atIndex:8];
        [encoder setBytes:&sw32 length:sizeof(sw32) atIndex:9];

        MTLSize gridSize = MTLSizeMake(out_width, out_height, batch_size * channels);
        NSUInteger w = MIN(pipeline.maxTotalThreadsPerThreadgroup, 16);
        MTLSize tgSize = MTLSizeMake(w, w, 1);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:tgSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(outputBuf, output_size);
    }
}

// AvgPool2D
LEAN_EXPORT lean_obj_res scilean_metal_avgpool2d_f32(
    size_t batch_size,
    size_t channels,
    size_t in_height,
    size_t in_width,
    size_t pool_h,
    size_t pool_w,
    size_t stride_h,
    size_t stride_w,
    b_lean_obj_arg input_arr
) {
    if (!ensure_metal_initialized()) {
        return empty_byte_array_f32();
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"avgpool2d");
        if (!pipeline) {
            NSLog(@"AvgPool2D: Failed to get pipeline");
            return empty_byte_array_f32();
        }

        size_t out_height = (in_height - pool_h) / stride_h + 1;
        size_t out_width = (in_width - pool_w) / stride_w + 1;

        size_t input_size = batch_size * channels * in_height * in_width;
        size_t output_size = batch_size * channels * out_height * out_width;

        id<MTLBuffer> inputBuf = create_buffer_from_byte_array_f32(input_arr, input_size, true);
        id<MTLBuffer> outputBuf = [device newBufferWithLength:output_size * sizeof(float)
                                                      options:MTLResourceStorageModeShared];

        uint32_t batch32 = (uint32_t)batch_size;
        uint32_t c32 = (uint32_t)channels;
        uint32_t ih32 = (uint32_t)in_height;
        uint32_t iw32 = (uint32_t)in_width;
        uint32_t ph32 = (uint32_t)pool_h;
        uint32_t pw32 = (uint32_t)pool_w;
        uint32_t sh32 = (uint32_t)stride_h;
        uint32_t sw32 = (uint32_t)stride_w;

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:inputBuf offset:0 atIndex:0];
        [encoder setBuffer:outputBuf offset:0 atIndex:1];
        [encoder setBytes:&batch32 length:sizeof(batch32) atIndex:2];
        [encoder setBytes:&c32 length:sizeof(c32) atIndex:3];
        [encoder setBytes:&ih32 length:sizeof(ih32) atIndex:4];
        [encoder setBytes:&iw32 length:sizeof(iw32) atIndex:5];
        [encoder setBytes:&ph32 length:sizeof(ph32) atIndex:6];
        [encoder setBytes:&pw32 length:sizeof(pw32) atIndex:7];
        [encoder setBytes:&sh32 length:sizeof(sh32) atIndex:8];
        [encoder setBytes:&sw32 length:sizeof(sw32) atIndex:9];

        MTLSize gridSize = MTLSizeMake(out_width, out_height, batch_size * channels);
        NSUInteger w = MIN(pipeline.maxTotalThreadsPerThreadgroup, 16);
        MTLSize tgSize = MTLSizeMake(w, w, 1);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:tgSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(outputBuf, output_size);
    }
}

// Global Average Pooling - reduces spatial dimensions to 1x1
LEAN_EXPORT lean_obj_res scilean_metal_global_avgpool2d_f32(
    size_t batch_size,
    size_t channels,
    size_t height,
    size_t width,
    b_lean_obj_arg input_arr
) {
    if (!ensure_metal_initialized()) {
        return empty_byte_array_f32();
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"global_avgpool2d");
        if (!pipeline) {
            NSLog(@"GlobalAvgPool2D: Failed to get pipeline");
            return empty_byte_array_f32();
        }

        size_t input_size = batch_size * channels * height * width;
        size_t output_size = batch_size * channels;

        id<MTLBuffer> inputBuf = create_buffer_from_byte_array_f32(input_arr, input_size, true);
        id<MTLBuffer> outputBuf = [device newBufferWithLength:output_size * sizeof(float)
                                                      options:MTLResourceStorageModeShared];

        uint32_t batch32 = (uint32_t)batch_size;
        uint32_t c32 = (uint32_t)channels;
        uint32_t h32 = (uint32_t)height;
        uint32_t w32 = (uint32_t)width;

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:inputBuf offset:0 atIndex:0];
        [encoder setBuffer:outputBuf offset:0 atIndex:1];
        [encoder setBytes:&batch32 length:sizeof(batch32) atIndex:2];
        [encoder setBytes:&c32 length:sizeof(c32) atIndex:3];
        [encoder setBytes:&h32 length:sizeof(h32) atIndex:4];
        [encoder setBytes:&w32 length:sizeof(w32) atIndex:5];

        MTLSize gridSize = MTLSizeMake(batch_size, channels, 1);
        NSUInteger tg = MIN(pipeline.maxTotalThreadsPerThreadgroup, 256);
        MTLSize tgSize = MTLSizeMake(MIN(tg, batch_size), 1, 1);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:tgSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(outputBuf, output_size);
    }
}

// BatchNorm2D inference
LEAN_EXPORT lean_obj_res scilean_metal_batchnorm2d_f32(
    size_t batch_size,
    size_t channels,
    size_t height,
    size_t width,
    float eps,
    uint8_t apply_relu,
    b_lean_obj_arg input_arr,
    b_lean_obj_arg gamma_arr,
    b_lean_obj_arg beta_arr,
    b_lean_obj_arg mean_arr,
    b_lean_obj_arg var_arr
) {
    if (!ensure_metal_initialized()) {
        return empty_byte_array_f32();
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"batchnorm2d_inference");
        if (!pipeline) {
            NSLog(@"BatchNorm2D: Failed to get pipeline");
            return empty_byte_array_f32();
        }

        size_t spatial_size = batch_size * channels * height * width;

        id<MTLBuffer> inputBuf = create_buffer_from_byte_array_f32(input_arr, spatial_size, true);
        id<MTLBuffer> gammaBuf = create_buffer_from_byte_array_f32(gamma_arr, channels, true);
        id<MTLBuffer> betaBuf = create_buffer_from_byte_array_f32(beta_arr, channels, true);
        id<MTLBuffer> meanBuf = create_buffer_from_byte_array_f32(mean_arr, channels, true);
        id<MTLBuffer> varBuf = create_buffer_from_byte_array_f32(var_arr, channels, true);
        id<MTLBuffer> outputBuf = [device newBufferWithLength:spatial_size * sizeof(float)
                                                      options:MTLResourceStorageModeShared];

        uint32_t batch32 = (uint32_t)batch_size;
        uint32_t c32 = (uint32_t)channels;
        uint32_t h32 = (uint32_t)height;
        uint32_t w32 = (uint32_t)width;
        uint32_t relu32 = (uint32_t)apply_relu;

        id<MTLCommandBuffer> commandBuffer = [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:inputBuf offset:0 atIndex:0];
        [encoder setBuffer:gammaBuf offset:0 atIndex:1];
        [encoder setBuffer:betaBuf offset:0 atIndex:2];
        [encoder setBuffer:meanBuf offset:0 atIndex:3];
        [encoder setBuffer:varBuf offset:0 atIndex:4];
        [encoder setBuffer:outputBuf offset:0 atIndex:5];
        [encoder setBytes:&batch32 length:sizeof(batch32) atIndex:6];
        [encoder setBytes:&c32 length:sizeof(c32) atIndex:7];
        [encoder setBytes:&h32 length:sizeof(h32) atIndex:8];
        [encoder setBytes:&w32 length:sizeof(w32) atIndex:9];
        [encoder setBytes:&eps length:sizeof(eps) atIndex:10];
        [encoder setBytes:&relu32 length:sizeof(relu32) atIndex:11];

        MTLSize gridSize = MTLSizeMake(width, height, batch_size * channels);
        NSUInteger tgw = MIN(pipeline.maxTotalThreadsPerThreadgroup, 16);
        MTLSize tgSize = MTLSizeMake(tgw, tgw, 1);

        [encoder dispatchThreads:gridSize threadsPerThreadgroup:tgSize];
        [encoder endEncoding];

        [commandBuffer commit];
        [commandBuffer waitUntilCompleted];

        return buffer_to_byte_array_f32(outputBuf, spatial_size);
    }
}

// ============================================================================
// Additional GPU Operations for Training
// ============================================================================

// AXPY on GpuBuffer: y = a*x + y (in-place update, returns new buffer)
LEAN_EXPORT lean_obj_res scilean_gpu_axpy_f32(
    size_t n,
    double alpha,
    b_lean_obj_arg x_buf,
    b_lean_obj_arg y_buf,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> x = get_mtl_buffer(x_buf);
    id<MTLBuffer> y = get_mtl_buffer(y_buf);
    if (!x || !y) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"axpy_out");
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get axpy_out pipeline"));
        }

        size_t output_size = n * sizeof(float);
        id<MTLBuffer> output = get_pooled_buffer(output_size);
        if (!output) {
            output = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        float alpha_f = (float)alpha;
        uint32_t n32 = (uint32_t)n;

        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:x offset:0 atIndex:0];
        [encoder setBuffer:y offset:0 atIndex:1];
        [encoder setBuffer:output offset:0 atIndex:2];
        [encoder setBytes:&alpha_f length:sizeof(alpha_f) atIndex:3];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:4];

        MTLSize gridSize = MTLSizeMake(n, 1, 1);
        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, n);
        [encoder dispatchThreads:gridSize threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)];

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:output];
        }

        return lean_io_result_mk_ok(wrap_gpu_buffer(output, output_size));
    }
}

// Scale on GpuBuffer: y = a*x
LEAN_EXPORT lean_obj_res scilean_gpu_scale_f32(
    size_t n,
    double alpha,
    b_lean_obj_arg x_buf,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> x = get_mtl_buffer(x_buf);
    if (!x) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"scale_out");
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get scale_out pipeline"));
        }

        size_t output_size = n * sizeof(float);
        id<MTLBuffer> output = get_pooled_buffer(output_size);
        if (!output) {
            output = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        float alpha_f = (float)alpha;
        uint32_t n32 = (uint32_t)n;

        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:x offset:0 atIndex:0];
        [encoder setBuffer:output offset:0 atIndex:1];
        [encoder setBytes:&alpha_f length:sizeof(alpha_f) atIndex:2];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:3];

        MTLSize gridSize = MTLSizeMake(n, 1, 1);
        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, n);
        [encoder dispatchThreads:gridSize threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)];

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:output];
        }

        return lean_io_result_mk_ok(wrap_gpu_buffer(output, output_size));
    }
}

// Sub on GpuBuffer: z = x - y
LEAN_EXPORT lean_obj_res scilean_gpu_sub_f32(
    b_lean_obj_arg x_buf,
    b_lean_obj_arg y_buf,
    size_t n,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> x = get_mtl_buffer(x_buf);
    id<MTLBuffer> y = get_mtl_buffer(y_buf);
    if (!x || !y) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"sub_out");
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get sub_out pipeline"));
        }

        size_t output_size = n * sizeof(float);
        id<MTLBuffer> output = get_pooled_buffer(output_size);
        if (!output) {
            output = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        uint32_t n32 = (uint32_t)n;

        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:x offset:0 atIndex:0];
        [encoder setBuffer:y offset:0 atIndex:1];
        [encoder setBuffer:output offset:0 atIndex:2];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:3];

        MTLSize gridSize = MTLSizeMake(n, 1, 1);
        NSUInteger tgSize = MIN(pipeline.maxTotalThreadsPerThreadgroup, n);
        [encoder dispatchThreads:gridSize threadsPerThreadgroup:MTLSizeMake(tgSize, 1, 1)];

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:output];
        }

        return lean_io_result_mk_ok(wrap_gpu_buffer(output, output_size));
    }
}

// GEMM with first matrix transposed: C = A^T @ B
// A is [k, m], treated as A^T [m, k], B is [k, n], result C is [m, n]
LEAN_EXPORT lean_obj_res scilean_gpu_gemm_tn_f32(
    b_lean_obj_arg A_buf,
    b_lean_obj_arg B_buf,
    size_t m,
    size_t k,
    size_t n,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> A = get_mtl_buffer(A_buf);
    id<MTLBuffer> B = get_mtl_buffer(B_buf);
    if (!A || !B) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"gemm_tn");
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get gemm_tn pipeline"));
        }

        size_t output_size = m * n * sizeof(float);
        id<MTLBuffer> C = get_pooled_buffer(output_size);
        if (!C) {
            C = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        uint32_t m32 = (uint32_t)m;
        uint32_t k32 = (uint32_t)k;
        uint32_t n32 = (uint32_t)n;

        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:A offset:0 atIndex:0];
        [encoder setBuffer:B offset:0 atIndex:1];
        [encoder setBuffer:C offset:0 atIndex:2];
        [encoder setBytes:&m32 length:sizeof(m32) atIndex:3];
        [encoder setBytes:&k32 length:sizeof(k32) atIndex:4];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:5];

        // Tiled kernel: 32x32 tiles, threadgroup memory for As and Bs
        size_t tg_mem_size = 2048 * sizeof(float);  // As[32][32] + Bs[32][32]
        [encoder setThreadgroupMemoryLength:tg_mem_size atIndex:0];

        MTLSize gridSize = MTLSizeMake((n + 31) / 32, (m + 31) / 32, 1);
        MTLSize tgSize = MTLSizeMake(32, 32, 1);
        [encoder dispatchThreadgroups:gridSize threadsPerThreadgroup:tgSize];

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:C];
        }

        return lean_io_result_mk_ok(wrap_gpu_buffer(C, output_size));
    }
}

// GEMM with second matrix transposed: C = A @ B^T
// A is [m, k], B is [n, k], treated as B^T [k, n], result C is [m, n]
LEAN_EXPORT lean_obj_res scilean_gpu_gemm_nt_f32(
    b_lean_obj_arg A_buf,
    b_lean_obj_arg B_buf,
    size_t m,
    size_t k,
    size_t n,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> A = get_mtl_buffer(A_buf);
    id<MTLBuffer> B = get_mtl_buffer(B_buf);
    if (!A || !B) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        id<MTLComputePipelineState> pipeline = get_pipeline(@"gemm_nt");
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get gemm_nt pipeline"));
        }

        size_t output_size = m * n * sizeof(float);
        id<MTLBuffer> C = get_pooled_buffer(output_size);
        if (!C) {
            C = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        uint32_t m32 = (uint32_t)m;
        uint32_t k32 = (uint32_t)k;
        uint32_t n32 = (uint32_t)n;

        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:A offset:0 atIndex:0];
        [encoder setBuffer:B offset:0 atIndex:1];
        [encoder setBuffer:C offset:0 atIndex:2];
        [encoder setBytes:&m32 length:sizeof(m32) atIndex:3];
        [encoder setBytes:&k32 length:sizeof(k32) atIndex:4];
        [encoder setBytes:&n32 length:sizeof(n32) atIndex:5];

        // Tiled kernel: 32x32 tiles, threadgroup memory for As and Bs
        size_t tg_mem_size = 2048 * sizeof(float);  // As[32][32] + Bs[32][32]
        [encoder setThreadgroupMemoryLength:tg_mem_size atIndex:0];

        MTLSize gridSize = MTLSizeMake((n + 31) / 32, (m + 31) / 32, 1);
        MTLSize tgSize = MTLSizeMake(32, 32, 1);
        [encoder dispatchThreadgroups:gridSize threadsPerThreadgroup:tgSize];

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:C];
        }

        return lean_io_result_mk_ok(wrap_gpu_buffer(C, output_size));
    }
}

// Sum reduction on GpuBuffer
LEAN_EXPORT lean_obj_res scilean_gpu_sum_f32(
    b_lean_obj_arg x_buf,
    size_t n,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> x = get_mtl_buffer(x_buf);
    if (!x) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        // For simplicity, do CPU sum for now
        float* data = (float*)[x contents];
        float sum = 0.0f;
        for (size_t i = 0; i < n; i++) {
            sum += data[i];
        }
        return lean_io_result_mk_ok(lean_box_float(sum));
    }
}

// Column-wise sum: for each column j, compute sum of elements in that column
// Input is [rows, cols], output is [cols]
// This is what we need for gradient accumulation: sum over batch dimension
LEAN_EXPORT lean_obj_res scilean_gpu_row_sum_f32(
    b_lean_obj_arg x_buf,
    size_t rows,
    size_t cols,
    lean_obj_arg /* world */
) {
    if (!ensure_metal_initialized()) {
        return lean_io_result_mk_error(lean_mk_string("Metal not available"));
    }

    id<MTLBuffer> x = get_mtl_buffer(x_buf);
    if (!x) {
        return lean_io_result_mk_error(lean_mk_string("Invalid GpuBuffer"));
    }

    @autoreleasepool {
        // Output has 'cols' elements (sum over rows for each column)
        size_t output_size = cols * sizeof(float);
        id<MTLBuffer> output = get_pooled_buffer(output_size);
        if (!output) {
            output = [device newBufferWithLength:output_size options:MTLResourceStorageModeShared];
        }

        // Use simple kernel for small row counts, large kernel for big batches
        bool use_large = (rows > 256);
        id<MTLComputePipelineState> pipeline = get_pipeline(use_large ? @"col_sum_large" : @"col_sum_simple");
        if (!pipeline) {
            return lean_io_result_mk_error(lean_mk_string("Failed to get col_sum pipeline"));
        }

        uint32_t rows32 = (uint32_t)rows;
        uint32_t cols32 = (uint32_t)cols;

        bool batched = is_batch_mode();
        id<MTLCommandBuffer> commandBuffer = batched ? g_batch_command_buffer : [commandQueue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = batched ? g_batch_encoder : [commandBuffer computeCommandEncoder];

        [encoder setComputePipelineState:pipeline];
        [encoder setBuffer:x offset:0 atIndex:0];
        [encoder setBuffer:output offset:0 atIndex:1];
        [encoder setBytes:&rows32 length:sizeof(rows32) atIndex:2];
        [encoder setBytes:&cols32 length:sizeof(cols32) atIndex:3];

        if (use_large) {
            // Large kernel: one threadgroup per column, 256 threads per threadgroup
            size_t tg_mem_size = 256 * sizeof(float);
            [encoder setThreadgroupMemoryLength:tg_mem_size atIndex:0];
            MTLSize gridSize = MTLSizeMake(cols, 1, 1);
            MTLSize tgSize = MTLSizeMake(256, 1, 1);
            [encoder dispatchThreadgroups:gridSize threadsPerThreadgroup:tgSize];
        } else {
            // Simple kernel: one thread per column
            MTLSize gridSize = MTLSizeMake((cols + 255) / 256, 1, 1);
            MTLSize tgSize = MTLSizeMake(cols < 256 ? cols : 256, 1, 1);
            [encoder dispatchThreadgroups:gridSize threadsPerThreadgroup:tgSize];
        }

        if (!batched) {
            [encoder endEncoding];
            [commandBuffer commit];
            [commandBuffer waitUntilCompleted];
        } else {
            [g_batch_outputs addObject:output];
        }

        return lean_io_result_mk_ok(wrap_gpu_buffer(output, output_size));
    }
}

} // extern "C"
