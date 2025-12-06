import SciLean.FFI.Metal
import SciLean.FFI.Float32Array

open SciLean

def benchGemm (name : String) (gemm : USize → USize → USize → ByteArray → ByteArray → ByteArray)
    (n : Nat) (numIters : Nat) : IO Unit := do
  let amat := Metal.Float32.fill (n * n).toUSize (1.0 : Float32)
  let bmat := Metal.Float32.fill (n * n).toUSize (1.0 : Float32)

  -- Warmup
  for _ in [:3] do
    let _ := gemm n.toUSize n.toUSize n.toUSize amat bmat

  -- Benchmark
  let mut sizeAccum := 0
  let start ← IO.monoNanosNow
  for _ in [:numIters] do
    let r := gemm n.toUSize n.toUSize n.toUSize amat bmat
    sizeAccum := sizeAccum + r.size
  let finish ← IO.monoNanosNow

  let totalNs := finish - start
  let avgNs := totalNs / numIters
  let avgMs := avgNs.toFloat / 1_000_000.0
  let flops := 2.0 * n.toFloat * n.toFloat * n.toFloat
  let gflops := if avgNs > 0 then flops / avgNs.toFloat else 0.0
  let tflops := gflops / 1000.0

  if tflops >= 1.0 then
    IO.println s!"  {name}: {avgMs} ms, {tflops} TFLOP/s"
  else
    IO.println s!"  {name}: {avgMs} ms, {gflops} GFLOP/s"

def main : IO Unit := do
  IO.println "=== GEMM Kernel Comparison ==="
  IO.println "Comparing all available GEMM implementations\n"

  for n in [256, 512, 1024, 2048] do
    let numIters := if n >= 2048 then 5 else if n >= 1024 then 10 else 20
    IO.println s!"Matrix size: {n}×{n} (n={numIters} iterations)"

    -- Basic naive GEMM
    benchGemm "Naive      " Metal.Float32.gemm n numIters

    -- Tiled GEMM (32x32 tiles)
    benchGemm "Tiled      " Metal.Float32.gemmTiled n numIters

    -- Simdgroup GEMM (hardware matrix units)
    benchGemm "Simd       " Metal.Float32.gemmSimd n numIters

    -- Optimized simdgroup GEMM
    benchGemm "SimdOpt    " Metal.Float32.gemmSimdOpt n numIters

    -- M4-optimized GEMM (if n is multiple of 64)
    if n % 64 == 0 then
      benchGemm "M4         " Metal.Float32.gemmM4 n numIters

    -- M4-Pro: Double-buffered with software pipelining (if n is multiple of 64)
    if n % 64 == 0 then
      benchGemm "M4Pro      " Metal.Float32.gemmM4Pro n numIters

    -- M4-Max: Larger tiles (if m is multiple of 128)
    if n % 128 == 0 then
      benchGemm "M4Max      " Metal.Float32.gemmM4Max n numIters

    -- MPS (Metal Performance Shaders)
    benchGemm "MPS        " Metal.Float32.gemmMPS n numIters

    -- Accelerate (CPU AMX)
    benchGemm "Accelerate " Metal.Float32.gemmAccelerate n numIters

    IO.println ""

  IO.println "Done!"
