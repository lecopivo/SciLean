import SciLean.Kernel.Ops
import SciLean.Util.Benchmark

/-!
# Kernel GEMM Benchmark

Benchmarks the dtype-parametric C kernel GEMM implementation.
Tests both Float32 (NEON-optimized on ARM) and Float64 (scalar ikj) paths.
-/

open SciLean

namespace KernelGEMMBenchmark

/-- Black hole to prevent dead code elimination -/
def mkBlackHole : IO (IO.Ref Float) := IO.mkRef 0.0

def blackHole (ref : IO.Ref Float) (x : Float) : IO Unit := do
  let current ← ref.get
  ref.set (current + x)

/-- Simple timer using nanoseconds -/
def timeNs (action : IO α) : IO (α × Nat) := do
  let start ← IO.monoNanosNow
  let result ← action
  let stop ← IO.monoNanosNow
  return (result, stop - start)

/-- Seed and generate random data using kernel RNG -/
def randomData (dt : Kernel.DType) (n : Nat) : IO ByteArray := do
  let seed ← IO.rand 0 1000000
  let _ := Kernel.rngSeed seed.toUInt64
  return Kernel.Typed.randUniform dt n

/-- Run a benchmark n times and return average time in microseconds -/
def benchmarkUs (ref : IO.Ref Float) (name : String) (warmup n : Nat) (action : IO Float) : IO Nat := do
  -- Warmup
  for _ in [:warmup] do
    let v ← action
    blackHole ref v

  -- Timed runs
  let mut totalNs : Nat := 0
  for _ in [:n] do
    let (v, ns) ← timeNs action
    blackHole ref v
    totalNs := totalNs + ns

  let avgUs := totalNs / n / 1000
  IO.println s!"{name}: {avgUs}μs avg over {n} runs"
  return avgUs

def runBenchmarks : IO Unit := do
  IO.println "╔════════════════════════════════════════════════════════════╗"
  IO.println "║          SciLean Kernel GEMM Benchmark                     ║"
  IO.println "║          F32 (NEON on ARM) vs F64 (scalar ikj)             ║"
  IO.println "╚════════════════════════════════════════════════════════════╝\n"

  let ref ← mkBlackHole

  let sizes := [(64, 64, 64), (128, 128, 128), (256, 256, 256), (512, 512, 512)]

  for (m, k, n) in sizes do
    IO.println s!"\nGEMM: {m}×{k} @ {k}×{n} = {m}×{n}"
    IO.println (String.ofList (List.replicate 50 '-'))

    -- Generate random data for both dtypes
    let Af64 ← randomData .f64 (m * k)
    let Bf64 ← randomData .f64 (k * n)
    let Af32 ← randomData .f32 (m * k)
    let Bf32 ← randomData .f32 (k * n)

    -- Use IO.pure to break caching
    let Af64Ref : IO ByteArray := pure Af64
    let Bf64Ref : IO ByteArray := pure Bf64
    let Af32Ref : IO ByteArray := pure Af32
    let Bf32Ref : IO ByteArray := pure Bf32

    -- Calculate FLOPS (2*m*k*n for GEMM)
    let flops := 2 * m * k * n

    -- Benchmark F64 Kernel
    let usF64 ← benchmarkUs ref "Kernel F64 (ikj)" 3 10 do
      let A ← Af64Ref
      let B ← Bf64Ref
      let result := Kernel.Typed.gemm .f64 A B m k n
      pure (Kernel.Typed.sum .f64 result)

    -- Benchmark F32 Kernel (NEON on ARM)
    let usF32 ← benchmarkUs ref "Kernel F32 (NEON)" 3 10 do
      let A ← Af32Ref
      let B ← Bf32Ref
      let result := Kernel.Typed.gemm .f32 A B m k n
      pure (Kernel.Typed.sum .f32 result)

    -- Calculate and print GFLOP/s
    if usF64 > 0 then
      let gflops64 := flops.toFloat / usF64.toFloat / 1000.0
      IO.println s!"  Kernel F64: {gflops64.toString.take 6} GFLOP/s"

    if usF32 > 0 then
      let gflops32 := flops.toFloat / usF32.toFloat / 1000.0
      IO.println s!"  Kernel F32: {gflops32.toString.take 6} GFLOP/s"

    if usF64 > 0 && usF32 > 0 then
      let speedup := usF64.toFloat / usF32.toFloat
      if speedup > 1.0 then
        IO.println s!"  F32 is {speedup.toString.take 5}× faster than F64"
      else
        IO.println s!"  F64 is {(1.0/speedup).toString.take 5}× faster than F32"

  IO.println "\n\nBenchmark complete!"

def main : IO Unit := runBenchmarks

end KernelGEMMBenchmark

def main := KernelGEMMBenchmark.main
