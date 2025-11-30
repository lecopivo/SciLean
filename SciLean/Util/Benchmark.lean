/-!
# Benchmarking Utilities

Reusable benchmarking infrastructure for SciLean.
-/

namespace SciLean.Benchmark

/-- Repeat a character n times -/
def padRight (s : String) (width : Nat) (c : Char := ' ') : String :=
  let padding := if s.length < width then String.mk (List.replicate (width - s.length) c) else ""
  s ++ padding

/-- Configuration for a benchmark run -/
structure Config where
  warmupIterations : Nat := 3
  timedIterations : Nat := 10
  printProgress : Bool := false
  deriving Repr

/-- Result of a single benchmark -/
structure Result where
  name : String
  avgTimeNs : Nat
  minTimeNs : Nat
  maxTimeNs : Nat
  iterations : Nat
  deriving Repr, Inhabited

/-- Format time in appropriate units -/
def formatTime (ns : Nat) : String :=
  if ns >= 1_000_000_000 then
    s!"{ns.toFloat / 1_000_000_000.0}s"
  else if ns >= 1_000_000 then
    s!"{ns.toFloat / 1_000_000.0}ms"
  else if ns >= 1_000 then
    s!"{ns.toFloat / 1_000.0}us"
  else
    s!"{ns}ns"

/-- Pretty print a benchmark result -/
def Result.toString (r : Result) : String :=
  s!"{r.name}: {formatTime r.avgTimeNs} avg ({r.iterations} iterations)"

instance : ToString Result := ⟨Result.toString⟩

/-- Run a benchmark with the given configuration -/
def run [Monad m] [MonadLiftT IO m] (name : String) (config : Config := {})
    (f : Unit → m α) : m Result := do
  -- Warmup
  for _ in [0:config.warmupIterations] do
    let _ ← f ()

  -- Timed runs
  let mut times : Array Nat := #[]
  for i in [0:config.timedIterations] do
    let start ← liftM (m := IO) IO.monoNanosNow
    let _ ← f ()
    let elapsed := (← liftM (m := IO) IO.monoNanosNow) - start
    times := times.push elapsed
    if config.printProgress then
      liftM (m := IO) <| IO.print s!"\r{name}: iteration {i + 1}/{config.timedIterations}"

  if config.printProgress then
    liftM (m := IO) <| IO.println ""

  let sorted := times.toList.mergeSort (· ≤ ·)
  let total := times.foldl (· + ·) 0

  return {
    name := name
    avgTimeNs := total / config.timedIterations
    minTimeNs := sorted.head!
    maxTimeNs := sorted.getLast!
    iterations := config.timedIterations
  }

/-- Run a pure benchmark (forces evaluation) -/
def runPure (name : String) (config : Config := {}) (f : Unit → α) : IO Result := do
  run name config fun () => do
    let _ := f ()
    pure ()

/-- Print a comparison table of results -/
def printComparison (results : Array Result) : IO Unit := do
  IO.println "┌────────────────────────────────────┬────────────────┬──────────────────┐"
  IO.println "│ Benchmark                          │ Avg Time       │ Speedup          │"
  IO.println "├────────────────────────────────────┼────────────────┼──────────────────┤"

  let baseline := (results[0]?).map (·.avgTimeNs) |>.getD 1
  for r in results do
    let speedup := if r.avgTimeNs > 0 then baseline.toFloat / r.avgTimeNs.toFloat else 0
    let nameStr := padRight (r.name.take 34) 34
    let timeStr := padRight (formatTime r.avgTimeNs) 14
    let speedupStr := if speedup >= 1.05 then s!"{Float.round (speedup * 10) / 10}x faster"
                      else if speedup <= 0.95 then s!"{Float.round (10 / speedup) / 10}x slower"
                      else "baseline"
    IO.println s!"│ {nameStr} │ {timeStr} │ {padRight (speedupStr.take 16) 16} │"

  IO.println "└────────────────────────────────────┴────────────────┴──────────────────┘"

/-- Suite of related benchmarks -/
structure Suite where
  name : String
  description : String := ""
  results : Array Result := #[]
  deriving Repr

/-- Add a result to a suite -/
def Suite.add (s : Suite) (r : Result) : Suite :=
  { s with results := s.results.push r }

/-- Print a suite's results -/
def Suite.print (s : Suite) : IO Unit := do
  IO.println s!"\n{s.name}"
  IO.println (String.mk (List.replicate s.name.length '='))
  if s.description.length > 0 then
    IO.println s.description
  printComparison s.results

end SciLean.Benchmark
