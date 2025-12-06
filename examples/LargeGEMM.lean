import SciLean.FFI.Metal
import SciLean.FFI.Float32Array

open SciLean

def main : IO Unit := do
  IO.println "=== Large GEMM Performance Benchmark ==="
  IO.println "Warming up..."

  -- Extended warmup
  for _ in [:50] do
    let a := Metal.Float32.fill 4096 (1.0 : Float32)
    let b := Metal.Float32.fill 4096 (1.0 : Float32)
    let _ := Metal.Float32.gemm 64 64 64 a b

  IO.println "Running benchmarks..."

  for n in [64, 128, 256, 512, 1024, 2048] do
    let amat := Metal.Float32.fill (n * n).toUSize (1.0 : Float32)
    let bmat := Metal.Float32.fill (n * n).toUSize (1.0 : Float32)

    -- More iterations for smaller matrices
    let numIters := if n >= 2048 then 5 else if n >= 1024 then 20 else if n >= 512 then 50 else 100

    -- Warmup for this size
    for _ in [:5] do
      let _ := Metal.Float32.gemm n.toUSize n.toUSize n.toUSize amat bmat

    -- Time entire loop (like OverheadTest that got realistic numbers)
    let mut sizeAccum := 0
    let start ← IO.monoNanosNow
    for _ in [:numIters] do
      let r := Metal.Float32.gemm n.toUSize n.toUSize n.toUSize amat bmat
      sizeAccum := sizeAccum + r.size
    let finish ← IO.monoNanosNow

    let totalNs := finish - start
    let avgNs := totalNs / numIters
    let avgUs := avgNs.toFloat / 1000.0
    let avgMs := avgUs / 1000.0
    let flops := 2.0 * n.toFloat * n.toFloat * n.toFloat
    let gflops := if avgNs > 0 then flops / avgNs.toFloat else 0.0

    IO.println s!"gemm({n}×{n}): {avgMs} ms, {gflops} GFLOP/s (size={sizeAccum})"

  IO.println ""
  IO.println "Done!"
