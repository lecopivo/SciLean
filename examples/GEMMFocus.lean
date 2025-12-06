import SciLean.FFI.Metal
import SciLean.FFI.Float32Array

open SciLean

def benchGemm (name : String) (gemm : USize → USize → USize → ByteArray → ByteArray → ByteArray)
    (n : Nat) (numIters : Nat) : IO Unit := do
  let amat := Metal.Float32.fill (n * n).toUSize (1.0 : Float32)
  let bmat := Metal.Float32.fill (n * n).toUSize (1.0 : Float32)

  -- Warmup
  for _ in [:5] do
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
  IO.println "=== Focused GEMM Analysis ==="
  IO.println "Testing M4Pro, MPS, and Accelerate at various sizes\n"

  -- Test at power-of-2 sizes from 128 to 4096
  for log2n in [7, 8, 9, 10, 11, 12] do
    let n := 1 <<< log2n  -- 128, 256, 512, 1024, 2048, 4096
    let numIters := if n >= 2048 then 10 else if n >= 1024 then 20 else 50
    IO.println s!"Matrix size: {n}×{n} ({numIters} iterations)"

    -- Compare M4Pro with MPS and Accelerate
    if n % 64 == 0 then
      benchGemm "M4Pro      " Metal.Float32.gemmM4Pro n numIters
    benchGemm "MPS        " Metal.Float32.gemmMPS n numIters
    benchGemm "Accelerate " Metal.Float32.gemmAccelerate n numIters
    IO.println ""

  IO.println "Done!"
