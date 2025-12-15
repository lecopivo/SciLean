import SciLean
import SciLean.Util.Benchmark

/-!
# Random generation benchmark

This compares a few ways of generating random vectors:

1. `IO.rand` in a loop to build a `FloatArray`
2. `SciLean.Rand` (using `uniformI`) to build a `Float^[n]` in one state-thread

The goal is to keep this *fast* and *easy to run* as a smoke/perf test.
-/

open SciLean

namespace RandBenchmark

def rand01IO : IO Float := do
  let N : Nat := 10^16
  let i ← IO.rand 0 N
  return i.toFloat / N.toFloat

def FloatArray.random01 (n : Nat) : IO FloatArray := do
  let mut xs : FloatArray := .emptyWithCapacity n
  for _ in [0:n] do
    xs := xs.push (← rand01IO)
  return xs

def benchSize (n : Nat) : IO Unit := do
  let config : Benchmark.Config :=
    if n ≤ 100_000 then
      { warmupIterations := 2, timedIterations := 8 }
    else
      { warmupIterations := 1, timedIterations := 3 }
  let acc ← IO.mkRef (0 : Nat)

  IO.setRandSeed 0
  let ioRand ← Benchmark.run "IO.rand -> FloatArray" config fun () => do
    let xs ← FloatArray.random01 n
    acc.modify (· + xs.size)
    pure ()

  IO.setRandSeed 0
  let scileanRand ← Benchmark.run "SciLean.Rand -> Float^[n]" config fun () => do
    let xs : Float^[n] ← (DataArrayN.rand (I := Idx n) (uniformI Float)).get
    acc.modify (· + xs.data.size)
    pure ()

  let _ ← acc.get

  let mut suite : Benchmark.Suite := { name := s!"Random vector generation (n={n})" }
  suite := suite.add ioRand
  suite := suite.add scileanRand
  suite.print


def main : IO Unit := do
  IO.println "╔════════════════════════════════════════════════════════════╗"
  IO.println "║              SciLean Random Benchmark                      ║"
  IO.println "╚════════════════════════════════════════════════════════════╝"

  for n in [10_000, 100_000, 250_000, 1_000_000] do
    benchSize n

end RandBenchmark

def main := RandBenchmark.main
