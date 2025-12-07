-- Minimal Metal benchmark that doesn't require full SciLean (avoids Mathlib linker issues)
import SciLean.FFI.Metal
import SciLean.FFI.Float32Array

open SciLean

-- Timing helper for ByteArray operations
@[noinline] def timeByteArray (iters : Nat := 10) (compute : Unit → ByteArray) : IO Float := do
  let warmup := compute ()
  let _ := warmup.size
  let acc ← IO.mkRef (0 : Nat)
  let start ← IO.monoNanosNow
  for _ in [:iters] do
    let arr := compute ()
    acc.modify (· + arr.size)
  let stop ← IO.monoNanosNow
  let _ ← acc.get
  return (stop - start).toFloat / 1000000.0 / iters.toFloat

-- Generate Float32 test data
def generateFloat32Data (n : Nat) : ByteArray := Id.run do
  let mut arr := ByteArray.empty
  for _ in [:n * 4] do
    arr := arr.push 0
  for i in [:n] do
    let v : Float32 := Float.toFloat32 (i.toFloat * 0.001 + 1.0)
    arr := arr.usetFloat32 (i * 4).toUSize v
  return arr

def main : IO Unit := do
  IO.println "╔═══════════════════════════════════════════════════════════╗"
  IO.println "║     SciLean Metal GPU Benchmark (Minimal)                 ║"
  IO.println "╚═══════════════════════════════════════════════════════════╝"

  if !Metal.isAvailable () then
    IO.println "\nMetal GPU: Not available"
    return

  IO.println "\nMetal GPU: Available"
  IO.println ""

  -- GEMM Comparison
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "GEMM KERNEL COMPARISON"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""

  for n in [512, 1024, 2048] do
    let matA32 := generateFloat32Data (n * n)
    let matB32 := generateFloat32Data (n * n)
    let flops := 2.0 * n.toFloat * n.toFloat * n.toFloat / 1e9

    -- Naive
    let naiveMs ← timeByteArray 5 (fun () => Metal.Float32.gemm n.toUSize n.toUSize n.toUSize matA32 matB32)
    let gflopsNaive := if naiveMs > 0.001 then flops / (naiveMs / 1000.0) else 0.0

    -- Tiled
    let tiledMs ← timeByteArray 5 (fun () => Metal.Float32.gemmTiled n.toUSize n.toUSize n.toUSize matA32 matB32)
    let gflopsTiled := if tiledMs > 0.001 then flops / (tiledMs / 1000.0) else 0.0

    -- Simdgroup
    let simdMs ← timeByteArray 5 (fun () => Metal.Float32.gemmSimd n.toUSize n.toUSize n.toUSize matA32 matB32)
    let gflopsSimd := if simdMs > 0.001 then flops / (simdMs / 1000.0) else 0.0

    -- MPS (Apple's optimized library)
    let mpsMs ← timeByteArray 5 (fun () => Metal.Float32.gemmMPS n.toUSize n.toUSize n.toUSize matA32 matB32)
    let gflopsMPS := if mpsMs > 0.001 then flops / (mpsMs / 1000.0) else 0.0

    IO.println s!"  {n}×{n} ({flops.toString.take 5} GFLOPS):"
    IO.println s!"    Naive:   {naiveMs.toString.take 7}ms  {gflopsNaive.toString.take 6} GFLOP/s"
    IO.println s!"    Tiled:   {tiledMs.toString.take 7}ms  {gflopsTiled.toString.take 6} GFLOP/s"
    IO.println s!"    Simd:    {simdMs.toString.take 7}ms  {gflopsSimd.toString.take 6} GFLOP/s"
    IO.println s!"    MPS:     {mpsMs.toString.take 7}ms  {gflopsMPS.toString.take 6} GFLOP/s"
    IO.println ""

  -- Flash Attention
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "FLASH ATTENTION"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "softmax(Q @ K^T / sqrt(d)) @ V"
  IO.println ""

  for (seqLen, headDim) in [(128, 64), (256, 64), (512, 64), (1024, 64)] do
    let Q := generateFloat32Data (seqLen * headDim)
    let K := generateFloat32Data (seqLen * headDim)
    let V := generateFloat32Data (seqLen * headDim)
    let flops := 4.0 * seqLen.toFloat * seqLen.toFloat * headDim.toFloat / 1e9

    let attnMs ← timeByteArray 10 (fun () =>
      Metal.Float32.flashAttention seqLen.toUSize headDim.toUSize Q K V)
    let gflops := if attnMs > 0.001 then flops / (attnMs / 1000.0) else 0.0
    IO.println s!"  seq={seqLen}, d={headDim}: {attnMs.toString.take 8}ms ({gflops.toString.take 6} GFLOP/s)"

  -- Causal Attention
  IO.println ""
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "CAUSAL ATTENTION (masked)"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""

  for (seqLen, headDim) in [(128, 64), (256, 64), (512, 64)] do
    let Q := generateFloat32Data (seqLen * headDim)
    let K := generateFloat32Data (seqLen * headDim)
    let V := generateFloat32Data (seqLen * headDim)
    let flops := 2.0 * seqLen.toFloat * seqLen.toFloat * headDim.toFloat / 1e9

    let attnMs ← timeByteArray 10 (fun () =>
      Metal.Float32.flashAttentionCausal seqLen.toUSize headDim.toUSize Q K V)
    let gflops := if attnMs > 0.001 then flops / (attnMs / 1000.0) else 0.0
    IO.println s!"  seq={seqLen}, d={headDim}: {attnMs.toString.take 8}ms ({gflops.toString.take 6} GFLOP/s)"

  -- Softmax
  IO.println ""
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "SOFTMAX"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""

  for n in [10000, 100000, 1000000] do
    let data := generateFloat32Data n
    let sftmxMs ← timeByteArray 10 (fun () => Metal.Float32.softmax n.toUSize data)
    IO.println s!"  N={n}: {sftmxMs.toString.take 8}ms"

  -- Reduce Sum
  IO.println ""
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "REDUCE SUM"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""

  for n in [100000, 1000000, 10000000] do
    let data := generateFloat32Data n
    let start ← IO.monoNanosNow
    for _ in [:10] do
      let _ := Metal.Float32.reduceSum n.toUSize data
    let stop ← IO.monoNanosNow
    let ms := (stop - start).toFloat / 1000000.0 / 10.0
    IO.println s!"  N={n}: {ms.toString.take 8}ms"

  IO.println ""
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "Benchmark complete!"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""
  IO.println "Compare with MLX/PyTorch: uv run benchmarks/mlx_pytorch_comparison.py"
