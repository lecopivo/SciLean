-- Benchmark Float32 (native) vs Float64 (with conversion) on Metal GPU
import SciLean.FFI.Metal
import SciLean.FFI.Float32Array

open SciLean

-- Timing helpers that force evaluation by using results

-- For FloatArray-returning operations (Float64)
@[noinline] def timeFloatArray (iters : Nat := 10) (compute : Unit → FloatArray) : IO Float := do
  let warmup := compute ()
  let _ := warmup.size  -- force evaluation
  let acc ← IO.mkRef (0 : Nat)
  let start ← IO.monoNanosNow
  for _ in [:iters] do
    let arr := compute ()
    acc.modify (· + arr.size)
  let stop ← IO.monoNanosNow
  let _ ← acc.get
  return (stop - start).toFloat / 1000000.0 / iters.toFloat

-- For ByteArray-returning operations (Float32)
@[noinline] def timeByteArray (iters : Nat := 10) (compute : Unit → ByteArray) : IO Float := do
  let warmup := compute ()
  let _ := warmup.size  -- force evaluation
  let acc ← IO.mkRef (0 : Nat)
  let start ← IO.monoNanosNow
  for _ in [:iters] do
    let arr := compute ()
    acc.modify (· + arr.size)
  let stop ← IO.monoNanosNow
  let _ ← acc.get
  return (stop - start).toFloat / 1000000.0 / iters.toFloat

-- For Float-returning operations (reductions)
@[noinline] def timeFloat (iters : Nat := 10) (compute : Unit → Float) : IO Float := do
  let warmup := compute ()
  let _ := warmup  -- force evaluation
  let acc ← IO.mkRef (0.0 : Float)
  let start ← IO.monoNanosNow
  for _ in [:iters] do
    let v := compute ()
    acc.modify (· + v * 0.0000001)  -- Use result to prevent elimination
  let stop ← IO.monoNanosNow
  let _ ← acc.get
  return (stop - start).toFloat / 1000000.0 / iters.toFloat

-- For Float32-returning operations (reductions)
@[noinline] def timeFloat32 (iters : Nat := 10) (compute : Unit → Float32) : IO Float := do
  let warmup := compute ()
  let _ := warmup  -- force evaluation
  let acc ← IO.mkRef (0.0 : Float)
  let start ← IO.monoNanosNow
  for _ in [:iters] do
    let v := compute ()
    acc.modify (· + Float32.toFloat v * 0.0000001)  -- Use result
  let stop ← IO.monoNanosNow
  let _ ← acc.get
  return (stop - start).toFloat / 1000000.0 / iters.toFloat

-- Generate test data
def generateFloat64Data (n : Nat) : FloatArray :=
  FloatArray.mk (Array.range n |>.map fun i => i.toFloat * 0.001 + 1.0)

def generateFloat32Data (n : Nat) : ByteArray := Id.run do
  let mut arr := ByteArray.empty
  for _ in [:n * 4] do
    arr := arr.push 0
  for i in [:n] do
    let v : Float32 := Float.toFloat32 (i.toFloat * 0.001 + 1.0)
    arr := arr.usetFloat32 (i * 4).toUSize v
  return arr

def formatSpeedup (t1 t2 : Float) : String :=
  if t2 > 0.001 && t1 > 0.001 then
    let speedup := t1 / t2
    if speedup >= 1.0 then s!"Float32 {speedup.toString.take 5}x faster"
    else s!"Float64 {(1.0/speedup).toString.take 5}x faster"
  else "Both instant"

def main : IO Unit := do
  IO.println "╔═══════════════════════════════════════════════════════════╗"
  IO.println "║    Float32 (Native) vs Float64 (Conversion) Benchmark     ║"
  IO.println "╚═══════════════════════════════════════════════════════════╝"

  if !Metal.isAvailable () then
    IO.println "\nMetal GPU: Not available ✗"
    return

  IO.println "\nMetal GPU: Available ✓"
  IO.println "\nFloat64: Lean stores double, Metal uses float → conversion overhead"
  IO.println "Float32: Lean stores float via ByteArray → zero conversion\n"

  -- ═══════════════════════════════════════════════════════════
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "FILL OPERATION"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  for size in [100000, 1000000, 10000000] do
    let f64Ms ← timeFloatArray 10 (fun () => Metal.fill size.toUSize 3.14)
    let f32Ms ← timeByteArray 10 (fun () => Metal.Float32.fill size.toUSize (3.14 : Float32))
    IO.println s!"  N={size}: Float64 {f64Ms.toString.take 8}ms, Float32 {f32Ms.toString.take 8}ms  ({formatSpeedup f64Ms f32Ms})"

  -- ═══════════════════════════════════════════════════════════
  IO.println "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "ADDITION"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  for size in [100000, 1000000, 10000000] do
    let a64 := generateFloat64Data size
    let b64 := generateFloat64Data size
    let a32 := generateFloat32Data size
    let b32 := generateFloat32Data size
    let f64Ms ← timeFloatArray 10 (fun () => Metal.add size.toUSize a64 b64)
    let f32Ms ← timeByteArray 10 (fun () => Metal.Float32.add size.toUSize a32 b32)
    IO.println s!"  N={size}: Float64 {f64Ms.toString.take 8}ms, Float32 {f32Ms.toString.take 8}ms  ({formatSpeedup f64Ms f32Ms})"

  -- ═══════════════════════════════════════════════════════════
  IO.println "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "REDUCE SUM"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  for size in [100000, 1000000, 10000000] do
    let data64 := generateFloat64Data size
    let data32 := generateFloat32Data size
    let f64Ms ← timeFloat 10 (fun () => Metal.reduceSum size.toUSize data64)
    let f32Ms ← timeFloat32 10 (fun () => Metal.Float32.reduceSum size.toUSize data32)
    IO.println s!"  N={size}: Float64 {f64Ms.toString.take 8}ms, Float32 {f32Ms.toString.take 8}ms  ({formatSpeedup f64Ms f32Ms})"

  -- ═══════════════════════════════════════════════════════════
  IO.println "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "MATRIX MULTIPLY (GEMM) - Naive"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  for n in [256, 512, 1024] do
    let matA64 := generateFloat64Data (n * n)
    let matB64 := generateFloat64Data (n * n)
    let matA32 := generateFloat32Data (n * n)
    let matB32 := generateFloat32Data (n * n)
    let f64Ms ← timeFloatArray 5 (fun () => Metal.gemm n.toUSize n.toUSize n.toUSize matA64 matB64)
    let f32Ms ← timeByteArray 5 (fun () => Metal.Float32.gemm n.toUSize n.toUSize n.toUSize matA32 matB32)
    let flops := 2.0 * n.toFloat * n.toFloat * n.toFloat / 1e9
    let gflops64 := if f64Ms > 0.001 then flops / (f64Ms / 1000.0) else 0.0
    let gflops32 := if f32Ms > 0.001 then flops / (f32Ms / 1000.0) else 0.0
    IO.println s!"  {n}x{n}: Float64 {f64Ms.toString.take 6}ms ({gflops64.toString.take 5} GFLOP/s), Float32 {f32Ms.toString.take 6}ms ({gflops32.toString.take 5} GFLOP/s)"

  -- ═══════════════════════════════════════════════════════════
  IO.println "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "GEMM KERNEL COMPARISON: Naive vs Tiled vs Simdgroup vs MPS"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "(MPS = Metal Performance Shaders, Apple's optimized library)\n"

  for n in [256, 512, 1024, 2048] do
    let matA32 := generateFloat32Data (n * n)
    let matB32 := generateFloat32Data (n * n)
    let flops := 2.0 * n.toFloat * n.toFloat * n.toFloat / 1e9

    -- Naive
    let naiveMs ← timeByteArray 5 (fun () => Metal.Float32.gemm n.toUSize n.toUSize n.toUSize matA32 matB32)
    let gflopsNaive := if naiveMs > 0.001 then flops / (naiveMs / 1000.0) else 0.0

    -- Tiled
    let tiledMs ← timeByteArray 5 (fun () => Metal.Float32.gemmTiled n.toUSize n.toUSize n.toUSize matA32 matB32)
    let gflopsTiled := if tiledMs > 0.001 then flops / (tiledMs / 1000.0) else 0.0

    -- Simdgroup (hardware matrix units)
    let simdMs ← timeByteArray 5 (fun () => Metal.Float32.gemmSimd n.toUSize n.toUSize n.toUSize matA32 matB32)
    let gflopsSimd := if simdMs > 0.001 then flops / (simdMs / 1000.0) else 0.0

    -- SimdOpt (shared memory prefetch + double buffering)
    let simdOptMs ← timeByteArray 5 (fun () => Metal.Float32.gemmSimdOpt n.toUSize n.toUSize n.toUSize matA32 matB32)
    let gflopsSimdOpt := if simdOptMs > 0.001 then flops / (simdOptMs / 1000.0) else 0.0

    -- MPS (Apple's optimized library)
    let mpsMs ← timeByteArray 5 (fun () => Metal.Float32.gemmMPS n.toUSize n.toUSize n.toUSize matA32 matB32)
    let gflopsMPS := if mpsMs > 0.001 then flops / (mpsMs / 1000.0) else 0.0

    let tiledSpeedup := if tiledMs > 0.001 then naiveMs / tiledMs else 0.0
    let simdSpeedup := if simdMs > 0.001 then naiveMs / simdMs else 0.0
    let simdOptSpeedup := if simdOptMs > 0.001 then naiveMs / simdOptMs else 0.0
    let mpsSpeedup := if mpsMs > 0.001 then naiveMs / mpsMs else 0.0

    IO.println s!"  {n}×{n} ({flops.toString.take 5} GFLOPS):"
    IO.println s!"    Naive:   {naiveMs.toString.take 7}ms  {gflopsNaive.toString.take 6} GFLOP/s"
    IO.println s!"    Tiled:   {tiledMs.toString.take 7}ms  {gflopsTiled.toString.take 6} GFLOP/s  ({tiledSpeedup.toString.take 4}x)"
    IO.println s!"    Simd:    {simdMs.toString.take 7}ms  {gflopsSimd.toString.take 6} GFLOP/s  ({simdSpeedup.toString.take 4}x)"
    IO.println s!"    SimdOpt: {simdOptMs.toString.take 7}ms  {gflopsSimdOpt.toString.take 6} GFLOP/s  ({simdOptSpeedup.toString.take 4}x)"
    IO.println s!"    MPS:     {mpsMs.toString.take 7}ms  {gflopsMPS.toString.take 6} GFLOP/s  ({mpsSpeedup.toString.take 4}x)"
    IO.println ""

  -- ═══════════════════════════════════════════════════════════
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "M4-OPTIMIZED GEMM (requires 128-aligned sizes)"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "(float4 loads, 128×128 tiles, no bounds checks)"
  IO.println ""

  for n in [1024, 2048, 4096] do
    let matA32 := generateFloat32Data (n * n)
    let matB32 := generateFloat32Data (n * n)
    let flops := 2.0 * n.toFloat * n.toFloat * n.toFloat / 1e9

    -- M4 optimized (float4 loads, 128×128 tiles)
    let m4Ms ← timeByteArray 5 (fun () => Metal.Float32.gemmM4 n.toUSize n.toUSize n.toUSize matA32 matB32)
    let gflopsM4 := if m4Ms > 0.001 then flops / (m4Ms / 1000.0) else 0.0

    -- Simd for comparison
    let simdMs ← timeByteArray 5 (fun () => Metal.Float32.gemmSimd n.toUSize n.toUSize n.toUSize matA32 matB32)
    let gflopsSimd := if simdMs > 0.001 then flops / (simdMs / 1000.0) else 0.0

    -- MPS for comparison
    let mpsMs ← timeByteArray 5 (fun () => Metal.Float32.gemmMPS n.toUSize n.toUSize n.toUSize matA32 matB32)
    let gflopsMPS := if mpsMs > 0.001 then flops / (mpsMs / 1000.0) else 0.0

    IO.println s!"  {n}×{n}:"
    IO.println s!"    M4:   {m4Ms.toString.take 7}ms  {gflopsM4.toString.take 6} GFLOP/s"
    IO.println s!"    Simd: {simdMs.toString.take 7}ms  {gflopsSimd.toString.take 6} GFLOP/s"
    IO.println s!"    MPS:  {mpsMs.toString.take 7}ms  {gflopsMPS.toString.take 6} GFLOP/s"
    IO.println ""

  -- ═══════════════════════════════════════════════════════════
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "LARGE MATRIX TEST"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  for n in [3072, 4096] do
    let matA32 := generateFloat32Data (n * n)
    let matB32 := generateFloat32Data (n * n)
    let flops := 2.0 * n.toFloat * n.toFloat * n.toFloat / 1e9

    let m4Ms ← timeByteArray 3 (fun () => Metal.Float32.gemmM4 n.toUSize n.toUSize n.toUSize matA32 matB32)
    let gflopsM4 := if m4Ms > 0.001 then flops / (m4Ms / 1000.0) else 0.0

    let mpsMs ← timeByteArray 3 (fun () => Metal.Float32.gemmMPS n.toUSize n.toUSize n.toUSize matA32 matB32)
    let gflopsMPS := if mpsMs > 0.001 then flops / (mpsMs / 1000.0) else 0.0

    IO.println s!"  {n}×{n}: M4 {m4Ms.toString.take 8}ms ({gflopsM4.toString.take 6} GFLOP/s), MPS {mpsMs.toString.take 8}ms ({gflopsMPS.toString.take 6} GFLOP/s)"

  -- ═══════════════════════════════════════════════════════════
  IO.println "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "AXPY TEST (y = a*x + y) - all ByteArray, zero-copy FFI"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  -- Scalar as ByteArray - same as vector data
  let aScalar := ByteArray.replicateFloat32 1 (2.5 : Float32)

  for size in [100000, 1000000, 10000000] do
    let x32 := generateFloat32Data size
    let y32 := generateFloat32Data size
    let axpyMs ← timeByteArray 10 (fun () => Metal.Float32.axpy size.toUSize aScalar x32 y32)
    -- Effective FLOPS: 2 ops per element (multiply + add)
    let flops := 2.0 * size.toFloat / 1e9
    let gflops := if axpyMs > 0.001 then flops / (axpyMs / 1000.0) else 0.0
    IO.println s!"  N={size}: {axpyMs.toString.take 8}ms ({gflops.toString.take 6} GFLOP/s)"

  -- ═══════════════════════════════════════════════════════════
  IO.println "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "MPS (GPU) vs ACCELERATE (CPU/AMX) COMPARISON"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "MPS: Metal Performance Shaders - runs on GPU"
  IO.println "Accelerate: Apple's BLAS - runs on CPU with AMX coprocessor\n"

  for n in [256, 512, 1024, 2048, 4096] do
    let matA32 := generateFloat32Data (n * n)
    let matB32 := generateFloat32Data (n * n)
    let flops := 2.0 * n.toFloat * n.toFloat * n.toFloat / 1e9

    let mpsMs ← timeByteArray 3 (fun () => Metal.Float32.gemmMPS n.toUSize n.toUSize n.toUSize matA32 matB32)
    let gflopsMPS := if mpsMs > 0.001 then flops / (mpsMs / 1000.0) else 0.0

    let accelMs ← timeByteArray 3 (fun () => Metal.Float32.gemmAccelerate n.toUSize n.toUSize n.toUSize matA32 matB32)
    let gflopsAccel := if accelMs > 0.001 then flops / (accelMs / 1000.0) else 0.0

    let winner := if gflopsMPS > gflopsAccel then "MPS (GPU)" else "Accelerate (AMX)"
    IO.println s!"  {n}×{n}:"
    IO.println s!"    MPS (GPU):          {mpsMs.toString.take 8}ms  {gflopsMPS.toString.take 6} GFLOP/s"
    IO.println s!"    Accelerate (AMX):   {accelMs.toString.take 8}ms  {gflopsAccel.toString.take 6} GFLOP/s"
    IO.println s!"    Winner: {winner}"
    IO.println ""

  -- ═══════════════════════════════════════════════════════════
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "FLASH ATTENTION (Single-Head)"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "softmax(Q @ K^T / sqrt(d)) @ V\n"

  for (seqLen, headDim) in [(128, 64), (256, 64), (512, 64), (1024, 64)] do
    let Q := generateFloat32Data (seqLen * headDim)
    let K := generateFloat32Data (seqLen * headDim)
    let V := generateFloat32Data (seqLen * headDim)
    let flops := 4.0 * seqLen.toFloat * seqLen.toFloat * headDim.toFloat / 1e9

    let attnMs ← timeByteArray 10 (fun () =>
      Metal.Float32.flashAttention seqLen.toUSize headDim.toUSize Q K V)
    let gflops := if attnMs > 0.001 then flops / (attnMs / 1000.0) else 0.0
    IO.println s!"  seq={seqLen}, d={headDim}: {attnMs.toString.take 8}ms ({gflops.toString.take 6} GFLOP/s)"

  -- ═══════════════════════════════════════════════════════════
  IO.println "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "CAUSAL ATTENTION (masked)"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  for (seqLen, headDim) in [(128, 64), (256, 64), (512, 64)] do
    let Q := generateFloat32Data (seqLen * headDim)
    let K := generateFloat32Data (seqLen * headDim)
    let V := generateFloat32Data (seqLen * headDim)
    let flops := 2.0 * seqLen.toFloat * seqLen.toFloat * headDim.toFloat / 1e9  -- causal ~half

    let attnMs ← timeByteArray 10 (fun () =>
      Metal.Float32.flashAttentionCausal seqLen.toUSize headDim.toUSize Q K V)
    let gflops := if attnMs > 0.001 then flops / (attnMs / 1000.0) else 0.0
    IO.println s!"  seq={seqLen}, d={headDim}: {attnMs.toString.take 8}ms ({gflops.toString.take 6} GFLOP/s)"

  -- ═══════════════════════════════════════════════════════════
  IO.println "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "SOFTMAX (comparison with MLX/PyTorch)"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  for n in [10000, 100000, 1000000] do
    let data := generateFloat32Data n
    let sftmxMs ← timeByteArray 10 (fun () => Metal.Float32.softmax n.toUSize data)
    IO.println s!"  N={n}: {sftmxMs.toString.take 8}ms"

  IO.println "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "Benchmark complete!"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "\nSummary:"
  IO.println "  MPS (GPU): Apple's Metal Performance Shaders library"
  IO.println "  Accelerate (AMX): Apple's CPU BLAS using AMX coprocessor"
  IO.println "  Flash Attention: Custom Metal kernel for transformer attention"
  IO.println "  Both are highly optimized - comparing helps understand workload"
