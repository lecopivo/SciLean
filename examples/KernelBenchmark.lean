/-
  Benchmark comparing Kernel ops to native Lean operations.
  This measures raw throughput of the C kernel for common operations.
-/
import SciLean.Kernel.Integration

open SciLean SciLean.Kernel

/-- Global accumulator to prevent dead code elimination.
    We use IO.Ref to force the runtime to actually compute values. -/
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

/-- Run a benchmark n times and report average time. -/
def benchmark (ref : IO.Ref Float) (name : String) (n : Nat) (action : IO Float) : IO Unit := do
  -- Warmup
  for _ in [:5] do
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

def main : IO Unit := do
  IO.println "=== Kernel Performance Benchmark ==="
  IO.println ""

  -- Create accumulator to prevent dead code elimination
  let ref ← mkBlackHole

  let _ := ArrayOps.seedRng 42

  -- ============================================================================
  -- Verify Timing Works
  -- ============================================================================
  IO.println "--- Timing verification ---"
  let startNs ← IO.monoNanosNow
  let mut acc : Nat := 0
  for i in [:1000000] do
    acc := acc + i
  let endNs ← IO.monoNanosNow
  IO.println s!"1M loop iterations: {(endNs - startNs) / 1000}μs (acc={acc})"
  IO.println s!"Raw nanoseconds: start={startNs}, end={endNs}, diff={endNs - startNs}"
  IO.println ""

  -- ============================================================================
  -- Elementwise Operations
  -- ============================================================================
  IO.println "--- Elementwise Operations (n=1M elements) ---"

  let n : Nat := 1000000
  let x : Float^[Idx n] := ArrayOps.randUniform
  let y : Float^[Idx n] := ArrayOps.randUniform
  IO.println s!"Allocated 2x 1M Float arrays (16MB total)"

  -- Verify add produces correct result
  let z := ArrayOps.add x y
  let sumZ := ArrayOps.sum z
  IO.println s!"Verification: sum(x+y) = {sumZ}"

  -- Use IO.pure to break any caching
  let xRef : IO (Float^[Idx n]) := pure x
  let yRef : IO (Float^[Idx n]) := pure y

  -- Warmup benchmark to prime timing infrastructure
  benchmark ref "warmup" 5 do
    let x' ← xRef
    let y' ← yRef
    let z := ArrayOps.add x' y'
    pure (ArrayOps.sum z)

  benchmark ref "add (1M)" 100 do
    let x' ← xRef
    let y' ← yRef
    let z := ArrayOps.add x' y'
    pure (ArrayOps.sum z)

  benchmark ref "mul (1M)" 100 do
    let x' ← xRef
    let y' ← yRef
    let z := ArrayOps.mul x' y'
    pure (ArrayOps.sum z)

  benchmark ref "exp (1M)" 100 do
    let x' ← xRef
    let z := ArrayOps.exp x'
    pure (ArrayOps.sum z)

  benchmark ref "sum (1M)" 100 do
    let x' ← xRef
    pure (ArrayOps.sum x')

  IO.println ""

  -- ============================================================================
  -- Matrix Operations
  -- ============================================================================
  IO.println "--- Matrix Operations ---"

  -- Small matrices
  let m := 128
  let k := 128
  let n' := 128
  let A128 : Float^[Idx m, Idx k] := ArrayOps.randUniform
  let B128 : Float^[Idx k, Idx n'] := ArrayOps.randUniform

  let A128Ref : IO (Float^[Idx m, Idx k]) := pure A128
  let B128Ref : IO (Float^[Idx k, Idx n']) := pure B128

  benchmark ref "gemm 128x128 @ 128x128" 50 do
    let A ← A128Ref
    let B ← B128Ref
    let C := ArrayOps.gemm A B
    pure (ArrayOps.sum C)

  -- Medium matrices
  let m2 := 512
  let k2 := 512
  let n2 := 512
  let A512 : Float^[Idx m2, Idx k2] := ArrayOps.randUniform
  let B512 : Float^[Idx k2, Idx n2] := ArrayOps.randUniform
  let A512Ref : IO (Float^[Idx m2, Idx k2]) := pure A512
  let B512Ref : IO (Float^[Idx k2, Idx n2]) := pure B512

  benchmark ref "gemm 512x512 @ 512x512" 10 do
    let A ← A512Ref
    let B ← B512Ref
    let C := ArrayOps.gemm A B
    pure (ArrayOps.sum C)

  -- Matrix-vector multiply
  let v128 : Float^[Idx k] := ArrayOps.randUniform
  let v128Ref : IO (Float^[Idx k]) := pure v128

  benchmark ref "gemv 128x128 @ 128" 100 do
    let A ← A128Ref
    let v ← v128Ref
    let y := ArrayOps.gemv A v
    pure (ArrayOps.sum y)

  IO.println ""

  -- ============================================================================
  -- Fused Operations
  -- ============================================================================
  IO.println "--- Fused Operations ---"

  let logits1k : Float^[Idx 1000] := ArrayOps.randUniform
  let logits1kRef : IO (Float^[Idx 1000]) := pure logits1k

  benchmark ref "softmax (1K)" 100 do
    let l ← logits1kRef
    let p := ArrayOps.softmax l
    pure (ArrayOps.sum p)

  -- Typical transformer attention softmax size
  let logits512 : Float^[Idx 512] := ArrayOps.randUniform
  let logits512Ref : IO (Float^[Idx 512]) := pure logits512

  benchmark ref "softmax (512 - attention)" 100 do
    let l ← logits512Ref
    let p := ArrayOps.softmax l
    pure (ArrayOps.sum p)

  IO.println ""

  -- ============================================================================
  -- Backward Pass Operations
  -- ============================================================================
  IO.println "--- Backward Pass (AD helpers) ---"

  let dC128 : Float^[Idx m, Idx n'] := ArrayOps.randUniform
  let dC128Ref : IO (Float^[Idx m, Idx n']) := pure dC128

  benchmark ref "gemm_backward_A 128x128" 50 do
    let B ← B128Ref
    let dC ← dC128Ref
    let dA := gemm_backward_A B dC
    pure (ArrayOps.sum dA)

  benchmark ref "gemm_backward_B 128x128" 50 do
    let A ← A128Ref
    let dC ← dC128Ref
    let dB := gemm_backward_B A dC
    pure (ArrayOps.sum dB)

  IO.println ""
  IO.println "=== Benchmark Complete ==="
