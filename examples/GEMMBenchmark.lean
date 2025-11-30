import SciLean
import SciLean.FFI.BLAS
import SciLean.Data.DataArray.TensorOperations
import SciLean.Util.Benchmark

/-!
# GEMM Benchmark

Benchmarks comparing naive matrix multiplication vs BLAS GEMM.
Tests both low-level FloatArray API and high-level DataArrayN API.
-/

open SciLean

namespace GEMMBenchmark

def rand01 : IO Float := do
  let N : Nat := 10^16
  let i ← IO.rand 0 N
  return i.toFloat / N.toFloat

def FloatArray.random (n : Nat) : IO FloatArray := do
  let mut xs : FloatArray := .emptyWithCapacity n
  for _ in [0:n] do
    xs := xs.push (← rand01)
  return xs

/-- Create random Float^[I,J] matrix -/
def DataArrayN.random {I nI} [IndexType I nI] {J nJ} [IndexType J nJ] : IO (Float^[I,J]) := do
  let mut arr : FloatArray := .emptyWithCapacity (nI * nJ)
  for _ in [0:(nI * nJ)] do
    arr := arr.push (← rand01)
  return DataArrayN.fromFloatArray arr

/-- Naive matrix multiplication: C = A * B -/
def naiveMatMul (m k n : Nat) (A B : FloatArray) : FloatArray := Id.run do
  let mut C : FloatArray := .emptyWithCapacity (m * n)
  for _ in [0:m*n] do
    C := C.push 0.0
  for i in [0:m] do
    for j in [0:n] do
      let mut sum := 0.0
      for l in [0:k] do
        let aik := A.uget (i*k + l).toUSize sorry_proof
        let bkj := B.uget (l*n + j).toUSize sorry_proof
        sum := sum + aik * bkj
      C := C.uset (i*n + j).toUSize sum sorry_proof
  return C

/-- BLAS GEMM: C = A * B -/
def blasMatMul (m k n : Nat) (A B : FloatArray) : FloatArray :=
  let C : FloatArray := .mk (Array.replicate (m * n) 0.0)
  BLAS.dgemmSimple m.toUSize n.toUSize k.toUSize 1.0 A B 0.0 C

/-- Verify correctness -/
def verifyGEMM (m k n : Nat) (A B : FloatArray) : IO Bool := do
  let naive := naiveMatMul m k n A B
  let blas := blasMatMul m k n A B
  let mut maxDiff := 0.0
  for i in [0:m*n] do
    let diff := Float.abs (naive.uget i.toUSize sorry_proof - blas.uget i.toUSize sorry_proof)
    if diff > maxDiff then
      maxDiff := diff
  IO.println s!"Max difference: {maxDiff}"
  return maxDiff < 1e-10

/-- Test high-level DataArrayN API -/
def testDataArrayNGEMM : IO Unit := do
  IO.println "\n╔════════════════════════════════════════════════════════════╗"
  IO.println "║         Testing DataArrayN BLAS Integration                ║"
  IO.println "╚════════════════════════════════════════════════════════════╝\n"

  -- 64x64 matrix multiplication
  let A : Float^[Idx 64, Idx 64] ← DataArrayN.random
  let B : Float^[Idx 64, Idx 64] ← DataArrayN.random
  let C : Float^[Idx 64, Idx 64] := 0

  -- Test contractMiddleAddRFloat (BLAS-backed)
  let resultBLAS : Float^[Idx 64, Idx 64] := DataArrayN.contractMiddleAddRFloat 1.0 A B 0.0 C

  -- Test naive version for comparison
  let resultNaive : Float^[Idx 64, Idx 64] := DataArrayN.contractMiddleAddRNaive 1.0 A B 0.0 C

  -- Compare results
  let mut maxDiff := 0.0
  for i in fullRange (Idx 64) do
    for j in fullRange (Idx 64) do
      let diff := Float.abs (resultBLAS[i,j] - resultNaive[i,j])
      if diff > maxDiff then
        maxDiff := diff

  IO.println s!"DataArrayN GEMM max difference: {maxDiff}"
  if maxDiff < 1e-10 then
    IO.println "✓ DataArrayN BLAS integration verified!"
  else
    IO.println "✗ ERROR: Results don't match!"

  -- Benchmark DataArrayN versions
  let config : Benchmark.Config := { warmupIterations := 2, timedIterations := 5 }

  let naiveResult ← Benchmark.run "DataArrayN Naive" config fun () => do
    let _ := DataArrayN.contractMiddleAddRNaive 1.0 A B 0.0 C
    pure ()

  let blasResult ← Benchmark.run "DataArrayN BLAS" config fun () => do
    let _ : Float^[Idx 64, Idx 64] := DataArrayN.contractMiddleAddRFloat 1.0 A B 0.0 C
    pure ()

  let mut suite : Benchmark.Suite := { name := "DataArrayN GEMM 64x64" }
  suite := suite.add naiveResult
  suite := suite.add blasResult
  suite.print

def runBenchmarks : IO Unit := do
  let sizes := [(64, 64, 64), (128, 128, 128), (256, 256, 256), (512, 512, 512)]

  IO.println "╔════════════════════════════════════════════════════════════╗"
  IO.println "║           SciLean BLAS GEMM Benchmark                      ║"
  IO.println "╚════════════════════════════════════════════════════════════╝"
  IO.println ""

  for (m, k, n) in sizes do
    IO.println s!"\nGEMM: {m}x{k} @ {k}x{n}"
    IO.println (String.ofList (List.replicate 40 '-'))

    let A ← FloatArray.random (m * k)
    let B ← FloatArray.random (k * n)

    -- Verify correctness first
    let correct ← verifyGEMM m k n A B
    if !correct then
      IO.println "ERROR: Results don't match!"
      continue

    let naiveConfig : Benchmark.Config := { warmupIterations := 1, timedIterations := 3 }
    let blasConfig : Benchmark.Config := { warmupIterations := 2, timedIterations := 10 }
    let mut suite : Benchmark.Suite := { name := s!"GEMM {m}x{k}x{n}" }

    -- Naive
    let naiveResult ← Benchmark.run "Naive loops" naiveConfig fun () => do
      let _ := naiveMatMul m k n A B
      pure ()
    suite := suite.add naiveResult

    -- BLAS
    let blasResult ← Benchmark.run "BLAS gemm" blasConfig fun () => do
      let _ := blasMatMul m k n A B
      pure ()
    suite := suite.add blasResult

    suite.print

  -- Test high-level DataArrayN API
  testDataArrayNGEMM

  IO.println "\nBenchmark complete!"

def main : IO Unit := runBenchmarks

end GEMMBenchmark

def main := GEMMBenchmark.main
