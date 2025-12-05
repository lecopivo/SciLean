-- Benchmark CPU vs Metal performance
import SciLean.FFI.Metal
import SciLean.Compiler.ComputeBackend

open SciLean.Compiler

-- Timing helper with multiple iterations (returns average milliseconds)
def timeItMs (iters : Nat := 10) (action : IO α) : IO (α × Float) := do
  -- Warmup
  let _ ← action
  -- Actual timing
  let start ← IO.monoNanosNow
  for _ in [:iters] do
    let _ ← action
  let result ← action
  let stop ← IO.monoNanosNow
  let elapsed := (stop - start).toFloat / 1000000.0 / (iters + 1).toFloat
  return (result, elapsed)

-- Time a FloatArray-producing thunk (forces fresh computation each iteration)
@[noinline] def timeArrayThunk (iters : Nat := 10) (compute : Unit → FloatArray) : IO Float := do
  -- Warmup
  let _ := compute ()
  -- Accumulator to force evaluation and prevent optimization
  let acc ← IO.mkRef (0 : Nat)
  -- Actual timing
  let start ← IO.monoNanosNow
  for _ in [:iters] do
    let arr := compute ()
    acc.modify (· + arr.size)
  let stop ← IO.monoNanosNow
  let _ ← acc.get  -- Ensure accumulator is read
  let elapsed := (stop - start).toFloat / 1000000.0 / iters.toFloat
  return elapsed

-- Time a Float-producing thunk
@[noinline] def timeFloatThunk (iters : Nat := 10) (compute : Unit → Float) : IO Float := do
  -- Warmup
  let _ := compute ()
  -- Accumulator to force evaluation
  let acc ← IO.mkRef (0.0 : Float)
  -- Actual timing
  let start ← IO.monoNanosNow
  for _ in [:iters] do
    let val := compute ()
    acc.modify (· + val)
  let stop ← IO.monoNanosNow
  let _ ← acc.get  -- Ensure accumulator is read
  let elapsed := (stop - start).toFloat / 1000000.0 / iters.toFloat
  return elapsed

-- Generate simple data efficiently (just incrementing values, no expensive trig)
def generateSimpleData (n : Nat) : FloatArray :=
  FloatArray.mk (Array.range n |>.map fun i => i.toFloat * 0.001 + 1.0)

-- CPU implementations
namespace CPUOps

def fill (n : Nat) (value : Float) : FloatArray :=
  FloatArray.mk (Array.range n |>.map fun _ => value)

def neg (x : FloatArray) : FloatArray :=
  FloatArray.mk (x.data.map (- ·))

def add (x y : FloatArray) : FloatArray :=
  FloatArray.mk (Array.zipWith (· + ·) x.data y.data)

def reduceSum (x : FloatArray) : Float :=
  x.data.foldl (· + ·) 0.0

def gemm (m k n : Nat) (A B : FloatArray) : FloatArray :=
  FloatArray.mk (Array.range m |>.flatMap fun i =>
    Array.range n |>.map fun j =>
      Array.range k |>.foldl (fun acc l =>
        acc + A.data[i * k + l]! * B.data[l * n + j]!) 0.0)

end CPUOps

-- Metal implementations
namespace MetalOps

def fill (n : Nat) (value : Float) : FloatArray :=
  SciLean.Metal.fill n.toUSize value

def neg (x : FloatArray) : FloatArray :=
  SciLean.Metal.neg x.size.toUSize x

def add (x y : FloatArray) : FloatArray :=
  SciLean.Metal.add x.size.toUSize x y

def reduceSum (x : FloatArray) : Float :=
  SciLean.Metal.reduceSum x.size.toUSize x

def gemm (m k n : Nat) (A B : FloatArray) : FloatArray :=
  SciLean.Metal.gemm m.toUSize k.toUSize n.toUSize A B

end MetalOps

-- Format speedup
def formatSpeedup (cpuMs metalMs : Float) : String :=
  if metalMs > 0.001 then
    let speedup := cpuMs / metalMs
    if speedup >= 1.0 then s!"Metal {speedup.toString.take 6}x faster"
    else s!"CPU {(1.0/speedup).toString.take 6}x faster"
  else if cpuMs > 0.001 then "Metal >> CPU"
  else "Both instant"

def main : IO Unit := do
  IO.println "╔═══════════════════════════════════════════════════════════╗"
  IO.println "║          CPU vs Metal GPU Benchmark                       ║"
  IO.println "╚═══════════════════════════════════════════════════════════╝"

  if !SciLean.Metal.isAvailable () then
    IO.println "\nMetal GPU: Not available ✗"
    return

  IO.println "\nMetal GPU: Available ✓\n"

  -- Warmup
  IO.println "Warming up..."
  let _ := MetalOps.fill 1000 1.0
  let _ := CPUOps.fill 1000 1.0

  -- ═══════════════════════════════════════════════════════════
  IO.println "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "FILL OPERATION (create array of N identical values)"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  for size in [10000, 100000, 1000000] do
    let cpuMs ← timeArrayThunk 10 (fun () => CPUOps.fill size 3.14)
    let metalMs ← timeArrayThunk 10 (fun () => MetalOps.fill size 3.14)
    IO.println s!"  N={size}: CPU {cpuMs.toString.take 8}ms, Metal {metalMs.toString.take 8}ms  ({formatSpeedup cpuMs metalMs})"

  -- ═══════════════════════════════════════════════════════════
  IO.println "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "NEGATION (element-wise negate N floats)"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  for size in [10000, 100000, 1000000] do
    let data := generateSimpleData size
    let cpuMs ← timeArrayThunk 10 (fun () => CPUOps.neg data)
    let metalMs ← timeArrayThunk 10 (fun () => MetalOps.neg data)
    IO.println s!"  N={size}: CPU {cpuMs.toString.take 8}ms, Metal {metalMs.toString.take 8}ms  ({formatSpeedup cpuMs metalMs})"

  -- ═══════════════════════════════════════════════════════════
  IO.println "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "ADDITION (element-wise add two arrays of N floats)"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  for size in [10000, 100000, 1000000] do
    let a := generateSimpleData size
    let b := generateSimpleData size
    let cpuMs ← timeArrayThunk 10 (fun () => CPUOps.add a b)
    let metalMs ← timeArrayThunk 10 (fun () => MetalOps.add a b)
    IO.println s!"  N={size}: CPU {cpuMs.toString.take 8}ms, Metal {metalMs.toString.take 8}ms  ({formatSpeedup cpuMs metalMs})"

  -- ═══════════════════════════════════════════════════════════
  IO.println "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "REDUCE SUM (sum N floats)"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  for size in [10000, 100000, 1000000] do
    let data := generateSimpleData size
    let cpuMs ← timeFloatThunk 10 (fun () => CPUOps.reduceSum data)
    let metalMs ← timeFloatThunk 10 (fun () => MetalOps.reduceSum data)
    IO.println s!"  N={size}: CPU {cpuMs.toString.take 8}ms, Metal {metalMs.toString.take 8}ms  ({formatSpeedup cpuMs metalMs})"

  -- ═══════════════════════════════════════════════════════════
  IO.println "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "MATRIX MULTIPLY (NxN @ NxN = O(N³) operations)"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  -- Small matrices: compare CPU vs Metal
  for n in [32, 64] do
    let matA := generateSimpleData (n * n)
    let matB := generateSimpleData (n * n)
    let cpuMs ← timeArrayThunk 5 (fun () => CPUOps.gemm n n n matA matB)
    let metalMs ← timeArrayThunk 5 (fun () => MetalOps.gemm n n n matA matB)
    IO.println s!"  {n}x{n}: CPU {cpuMs.toString.take 10}ms, Metal {metalMs.toString.take 8}ms  ({formatSpeedup cpuMs metalMs})"

  -- Large matrices: Metal only (CPU too slow)
  IO.println "\n  [Metal-only for larger matrices - CPU too slow]"
  for n in [128, 256, 512, 1024] do
    let matA := generateSimpleData (n * n)
    let matB := generateSimpleData (n * n)
    let metalMs ← timeArrayThunk 5 (fun () => MetalOps.gemm n n n matA matB)
    let flops := 2.0 * n.toFloat * n.toFloat * n.toFloat / 1e9  -- GFLOPs
    let gflops := if metalMs > 0.001 then flops / (metalMs / 1000.0) else 0.0
    IO.println s!"  {n}x{n}: Metal {metalMs.toString.take 8}ms  ({gflops.toString.take 6} GFLOP/s)"

  IO.println "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "Benchmark complete!"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
