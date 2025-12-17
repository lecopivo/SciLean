/-
GPU Batching Benchmark

Compares performance of batched vs unbatched GPU operations.
Batching reduces CPU-GPU synchronization overhead by combining
multiple operations into a single command buffer submission.
-/
import SciLean.FFI.Metal
import SciLean.FFI.Float32Array

open SciLean

/-- Create a ByteArray filled with random floats -/
def randomFloats (n : Nat) (seed : Nat) : ByteArray := Id.run do
  let mut arr := ByteArray.replicateFloat32 n 0.0
  let mut s := seed
  for i in List.range n do
    s := (s * 1103515245 + 12345) % (2^31)
    let val := (Float.ofNat (s % 1000)) / 1000.0
    arr := arr.usetFloat32 (i * 4).toUSize val.toFloat32
  return arr

/-- Measure time for an IO action -/
def timeIO (action : IO Unit) : IO Float := do
  let start ← IO.monoMsNow
  action
  let stop ← IO.monoMsNow
  return (Float.ofNat (stop - start))

/-- Run N operations WITHOUT batching (each op syncs separately) -/
def runUnbatched (n : Nat) (size : Nat) : IO Float := do
  let data := randomFloats size 42
  let gpu ← Metal.GpuBuffer.fromByteArray data

  timeIO do
    for _ in List.range n do
      let r1 ← Metal.GpuBuffer.relu gpu size.toUSize
      let r2 ← Metal.GpuBuffer.add r1 r1 size.toUSize
      let _ ← Metal.GpuBuffer.mul r2 gpu size.toUSize
      pure ()

/-- Run N operations WITH batching (single command buffer) -/
def runBatched (n : Nat) (size : Nat) : IO Float := do
  let data := randomFloats size 42
  let gpu ← Metal.GpuBuffer.fromByteArray data

  timeIO do
    for _ in List.range n do
      let _ ← Metal.withBatch do
        let r1 ← Metal.GpuBuffer.relu gpu size.toUSize
        let r2 ← Metal.GpuBuffer.add r1 r1 size.toUSize
        Metal.GpuBuffer.mul r2 gpu size.toUSize
      pure ()

/-- Run a chain of operations without batching -/
def runChainUnbatched (chainLen : Nat) (size : Nat) : IO Float := do
  let data := randomFloats size 42
  let gpu ← Metal.GpuBuffer.fromByteArray data

  timeIO do
    let mut current := gpu
    for _ in List.range chainLen do
      current ← Metal.GpuBuffer.relu current size.toUSize
    pure ()

/-- Run a chain of operations with batching -/
def runChainBatched (chainLen : Nat) (size : Nat) : IO Float := do
  let data := randomFloats size 42
  let gpu ← Metal.GpuBuffer.fromByteArray data

  timeIO do
    let _ ← Metal.withBatch do
      let mut current := gpu
      for _ in List.range chainLen do
        current ← Metal.GpuBuffer.relu current size.toUSize
      return current
    pure ()

def main : IO Unit := do
  if !Metal.isAvailable () then
    IO.println "Metal GPU not available"
    return

  IO.println "=== GPU Batching Benchmark ==="
  IO.println ""

  -- Warmup
  IO.println "Warming up GPU..."
  let _ ← runUnbatched 10 1024
  let _ ← runBatched 10 1024

  IO.println ""
  IO.println "--- Test 1: Multiple iterations (3 ops each) ---"
  IO.println "Each iteration does: relu → add → mul"
  IO.println ""

  for numIters in [10, 50, 100] do
    let size := 10000
    let unbatchedTime ← runUnbatched numIters size
    let batchedTime ← runBatched numIters size
    let speedup := unbatchedTime / (if batchedTime < 0.001 then 0.001 else batchedTime)

    IO.println s!"  {numIters} iterations, {size} elements:"
    IO.println s!"    Unbatched: {unbatchedTime} ms"
    IO.println s!"    Batched:   {batchedTime} ms"
    IO.println s!"    Speedup:   {speedup}x"
    IO.println ""

  IO.println "--- Test 2: Long chains (single iteration) ---"
  IO.println "Chain of N relu operations"
  IO.println ""

  for chainLen in [10, 50, 100, 200] do
    let size := 100000
    let unbatchedTime ← runChainUnbatched chainLen size
    let batchedTime ← runChainBatched chainLen size

    let speedup := unbatchedTime / (if batchedTime < 0.001 then 0.001 else batchedTime)

    IO.println s!"  Chain length {chainLen}, {size} elements:"
    IO.println s!"    Unbatched: {unbatchedTime} ms"
    IO.println s!"    Batched:   {batchedTime} ms"
    IO.println s!"    Speedup:   {speedup}x"
    IO.println ""

  IO.println "=== Benchmark Complete ==="
  IO.println ""
  IO.println "Note: Batching reduces CPU-GPU synchronization overhead."
  IO.println "For small/fast operations, the overhead reduction is significant."
  IO.println "For large/slow operations, the GPU compute time dominates."
