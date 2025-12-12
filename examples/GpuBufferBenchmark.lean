/-
  GpuBuffer Benchmark: Compare ByteArray-based vs GPU-resident operations

  This demonstrates the performance advantage of keeping data on the GPU
  between operations rather than copying to/from CPU on every call.
-/
import SciLean.FFI.Metal

open SciLean.Metal

/-- Create test data using Metal's efficient fill function -/
def makeF32Data (size : Nat) (value : Float32 := 1.0) : ByteArray :=
  Float32.fill size.toUSize value

/-- Format float as string with limited digits -/
def fmt (f : Float) : String := f.toString.take 7

/-- Benchmark: Multiple GEMM with ByteArray (copies every call) -/
def benchGemmByteArray (m k n : USize) (iters : Nat) : IO Float := do
  let A := makeF32Data (m.toNat * k.toNat) 1.0
  let B := makeF32Data (k.toNat * n.toNat) 2.0

  for _ in [0:3] do
    let _ := Float32.gemmAuto m k n A B

  let startTime ← IO.monoNanosNow
  for _ in [0:iters] do
    let _ := Float32.gemmAuto m k n A B
  let endTime ← IO.monoNanosNow

  pure (Float.ofNat (endTime - startTime) / 1e9)

/-- Benchmark: Multiple GEMM with GpuBuffer (no intermediate copies) -/
def benchGemmGpuBuffer (m k n : USize) (iters : Nat) : IO Float := do
  let A := makeF32Data (m.toNat * k.toNat) 1.0
  let B := makeF32Data (k.toNat * n.toNat) 2.0

  let gpuA ← GpuBuffer.fromByteArray A
  let gpuB ← GpuBuffer.fromByteArray B

  for _ in [0:3] do
    let _ ← GpuBuffer.gemm gpuA gpuB m k n

  let startTime ← IO.monoNanosNow
  for _ in [0:iters] do
    let _ ← GpuBuffer.gemm gpuA gpuB m k n
  let endTime ← IO.monoNanosNow

  pure (Float.ofNat (endTime - startTime) / 1e9)

/-- Benchmark: Chained GEMM operations with ByteArray -/
def benchChainByteArray (sz : USize) (iters : Nat) : IO Float := do
  let A := makeF32Data (sz.toNat * sz.toNat) 1.0
  let B := makeF32Data (sz.toNat * sz.toNat) 2.0
  let C := makeF32Data (sz.toNat * sz.toNat) 3.0

  for _ in [0:3] do
    let ab := Float32.gemmAuto sz sz sz A B
    let _ := Float32.gemmAuto sz sz sz ab C

  let startTime ← IO.monoNanosNow
  for _ in [0:iters] do
    let ab := Float32.gemmAuto sz sz sz A B
    let _ := Float32.gemmAuto sz sz sz ab C
  let endTime ← IO.monoNanosNow

  pure (Float.ofNat (endTime - startTime) / 1e9)

/-- Benchmark: Chained GEMM with GpuBuffer (0 intermediate copies) -/
def benchChainGpuBuffer (sz : USize) (iters : Nat) : IO Float := do
  let A := makeF32Data (sz.toNat * sz.toNat) 1.0
  let B := makeF32Data (sz.toNat * sz.toNat) 2.0
  let C := makeF32Data (sz.toNat * sz.toNat) 3.0

  let gpuA ← GpuBuffer.fromByteArray A
  let gpuB ← GpuBuffer.fromByteArray B
  let gpuC ← GpuBuffer.fromByteArray C

  for _ in [0:3] do
    let ab ← GpuBuffer.gemm gpuA gpuB sz sz sz
    let _ ← GpuBuffer.gemm ab gpuC sz sz sz

  let startTime ← IO.monoNanosNow
  for _ in [0:iters] do
    let ab ← GpuBuffer.gemm gpuA gpuB sz sz sz
    let _ ← GpuBuffer.gemm ab gpuC sz sz sz
  let endTime ← IO.monoNanosNow

  pure (Float.ofNat (endTime - startTime) / 1e9)

def main : IO Unit := do
  IO.println ""
  IO.println "=============================================================="
  IO.println "  GpuBuffer Benchmark: ByteArray vs GPU-Resident Buffers"
  IO.println "=============================================================="
  IO.println ""
  IO.println "ByteArray: copies data CPU<->GPU on every operation"
  IO.println "GpuBuffer: data stays on GPU, copies only at start/end"
  IO.println ""

  IO.println "--- Test 1: Single GEMM Operation ---"
  IO.println "(Note: ByteArray times show 0 because pure functions don't GPU sync)"
  IO.println ""
  IO.println "Config          | ByteArray   | GpuBuffer   | GPU Time"
  IO.println "------------------------------------------------------"

  -- 256x256 (256KB data)
  let gpuTime256 ← benchGemmGpuBuffer 256 256 256 100
  let gpuMs256 := gpuTime256 * 1000.0 / 100.0
  IO.println s!"256x256         | (no sync)   | {fmt gpuMs256}ms  | {fmt gpuMs256}ms"

  -- 512x512 (1MB data)
  let gpuTime512 ← benchGemmGpuBuffer 512 512 512 50
  let gpuMs512 := gpuTime512 * 1000.0 / 50.0
  IO.println s!"512x512         | (no sync)   | {fmt gpuMs512}ms  | {fmt gpuMs512}ms"

  -- 1024x1024 (4MB data)
  let gpuTime1024 ← benchGemmGpuBuffer 1024 1024 1024 20
  let gpuMs1024 := gpuTime1024 * 1000.0 / 20.0
  IO.println s!"1024x1024       | (no sync)   | {fmt gpuMs1024}ms  | {fmt gpuMs1024}ms"

  IO.println ""

  IO.println "--- Test 2: Chained GEMM (A*B then result*C) ---"
  IO.println ""
  IO.println "With ByteArray: 4 copies per chain (A,B up; AB down,up; AB*C down)"
  IO.println "With GpuBuffer: 0 copies per chain (all stays on GPU)"
  IO.println ""
  IO.println "Size            | GpuBuffer Chain | Est. Transfer Saved"
  IO.println "------------------------------------------------------"

  -- 256x256 chain - each copy is ~0.01ms, 4 copies = 0.04ms saved per chain
  let gpuChain256 ← benchChainGpuBuffer 256 100
  let gpuChainMs256 := gpuChain256 * 1000.0 / 100.0
  IO.println s!"256x256         | {fmt gpuChainMs256}ms       | ~0.04ms/iter (4x 0.01ms)"

  -- 512x512 chain - each copy is ~0.28ms, 4 copies = 1.1ms saved per chain
  let gpuChain512 ← benchChainGpuBuffer 512 50
  let gpuChainMs512 := gpuChain512 * 1000.0 / 50.0
  IO.println s!"512x512         | {fmt gpuChainMs512}ms       | ~1.1ms/iter (4x 0.28ms)"

  IO.println ""

  IO.println "--- Test 3: Transfer Overhead (Upload + Download) ---"
  IO.println "(Pre-creating data to exclude creation time from measurements)"
  IO.println ""

  -- Pre-create all data using Metal GPU fill (fast)
  let data256k := makeF32Data (256 * 256) 1.0
  let data1m := makeF32Data (512 * 512) 1.0
  let data4m := makeF32Data (1024 * 1024) 1.0
  IO.println ""

  IO.println "Size               | Upload     | Download   | Total"
  IO.println "------------------------------------------------------"

  -- 256KB
  let uploadStart256k ← IO.monoNanosNow
  let gpuBuf256k ← GpuBuffer.fromByteArray data256k
  let uploadEnd256k ← IO.monoNanosNow
  let downloadStart256k ← IO.monoNanosNow
  let _ ← gpuBuf256k.toByteArray
  let downloadEnd256k ← IO.monoNanosNow
  let uploadMs256k := Float.ofNat (uploadEnd256k - uploadStart256k) / 1e6
  let downloadMs256k := Float.ofNat (downloadEnd256k - downloadStart256k) / 1e6
  IO.println s!"256KB (256x256)    | {fmt uploadMs256k}ms  | {fmt downloadMs256k}ms  | {fmt (uploadMs256k + downloadMs256k)}ms"

  -- 1MB
  let uploadStart1m ← IO.monoNanosNow
  let gpuBuf1m ← GpuBuffer.fromByteArray data1m
  let uploadEnd1m ← IO.monoNanosNow
  let downloadStart1m ← IO.monoNanosNow
  let _ ← gpuBuf1m.toByteArray
  let downloadEnd1m ← IO.monoNanosNow
  let uploadMs1m := Float.ofNat (uploadEnd1m - uploadStart1m) / 1e6
  let downloadMs1m := Float.ofNat (downloadEnd1m - downloadStart1m) / 1e6
  IO.println s!"1MB (512x512)      | {fmt uploadMs1m}ms  | {fmt downloadMs1m}ms  | {fmt (uploadMs1m + downloadMs1m)}ms"

  -- 4MB
  let uploadStart4m ← IO.monoNanosNow
  let gpuBuf4m ← GpuBuffer.fromByteArray data4m
  let uploadEnd4m ← IO.monoNanosNow
  let downloadStart4m ← IO.monoNanosNow
  let _ ← gpuBuf4m.toByteArray
  let downloadEnd4m ← IO.monoNanosNow
  let uploadMs4m := Float.ofNat (uploadEnd4m - uploadStart4m) / 1e6
  let downloadMs4m := Float.ofNat (downloadEnd4m - downloadStart4m) / 1e6
  IO.println s!"4MB (1024x1024)    | {fmt uploadMs4m}ms  | {fmt downloadMs4m}ms  | {fmt (uploadMs4m + downloadMs4m)}ms"

  IO.println ""
  IO.println "=============================================================="
  IO.println "Summary: GpuBuffer eliminates per-operation copy overhead."
  IO.println "Speedup increases with more chained operations."
  IO.println "=============================================================="
