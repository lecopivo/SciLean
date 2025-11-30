import SciLean
import SciLean.FFI.Metal

open SciLean

def rand01 : IO Float := do
  let N : Nat := 10^16
  let i ← IO.rand 0 N
  return i.toFloat / N.toFloat

def FloatArray.rand01 (n : Nat) : IO FloatArray := do
  let mut xs : FloatArray := .mkEmpty n
  for _ in [0:n] do
    xs := xs.push (← _root_.rand01)
  return xs

-- CPU KMeans (baseline)
def kmeansCPU (d n k : Nat) (points centroids : FloatArray) : Float := Id.run do
  let mut loss := 0.0
  for i in [0:n] do
    let mut minNorm2 := Float.inf
    for j in [0:k] do
      let mut norm2 := 0.0
      for l in [0:d] do
        let xil := points.uget (i*d + l).toUSize sorry_proof
        let cjl := centroids.uget (j*d + l).toUSize sorry_proof
        norm2 := norm2 + (xil - cjl)*(xil - cjl)
      if norm2 < minNorm2 then
        minNorm2 := norm2
    loss := loss + minNorm2
  return loss

-- CPU Matrix multiply (baseline)
def gemmCPU (m k n : Nat) (A B : FloatArray) : FloatArray := Id.run do
  let mut C : FloatArray := .mkEmpty (m * n)
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

def benchmark (name : String) (warmup iterations : Nat) (f : Unit → IO α) : IO Unit := do
  -- Warmup
  for _ in [0:warmup] do
    let _ ← f ()

  -- Timed runs
  let start ← IO.monoNanosNow
  for _ in [0:iterations] do
    let _ ← f ()
  let elapsed := (← IO.monoNanosNow) - start
  let avgMs := (elapsed.toFloat / iterations.toFloat) / 1_000_000.0
  IO.println s!"{name}: {avgMs}ms avg over {iterations} iterations"

def main : IO Unit := do
  IO.println "SciLean Metal Benchmark"
  IO.println "======================"

  -- Check Metal availability
  IO.println ""
  let metalAvailable := Metal.isAvailable ()
  IO.println s!"Metal available: {metalAvailable}"

  -- KMeans benchmark
  IO.println ""
  IO.println "KMeans Benchmark (n=10000, d=64, k=32)"
  let d := 64
  let n := 10000
  let k := 32
  let points ← FloatArray.rand01 (n * d)
  let centroids ← FloatArray.rand01 (k * d)

  benchmark "CPU KMeans" 2 10 fun () => do
    return kmeansCPU d n k points centroids

  if metalAvailable then
    benchmark "GPU KMeans" 2 10 fun () => do
      return Metal.kmeans d.toUSize n.toUSize k.toUSize points centroids

  -- GEMM benchmark
  IO.println ""
  IO.println "GEMM Benchmark (512x512 × 512x512)"
  let m := 512
  let kk := 512
  let nn := 512
  let A ← FloatArray.rand01 (m * kk)
  let B ← FloatArray.rand01 (kk * nn)

  benchmark "CPU GEMM" 1 3 fun () => do
    return gemmCPU m kk nn A B

  if metalAvailable then
    benchmark "GPU GEMM" 1 10 fun () => do
      return Metal.gemm m.toUSize kk.toUSize nn.toUSize A B

  IO.println ""
  IO.println "Done!"
