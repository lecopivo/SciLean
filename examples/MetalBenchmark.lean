import SciLean
import SciLean.FFI.Metal
import SciLean.Util.Benchmark

open SciLean

namespace MetalBenchmark

def rand01 : IO Float := do
  let N : Nat := 10^16
  let i ← IO.rand 0 N
  return i.toFloat / N.toFloat

def FloatArray.random (n : Nat) : IO FloatArray := do
  let mut xs : FloatArray := .emptyWithCapacity n
  for _ in [0:n] do
    xs := xs.push (← rand01)
  return xs

-- CPU KMeans (naive baseline)
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

-- CPU Matrix multiply (naive baseline)
def gemmCPU (m k n : Nat) (A B : FloatArray) : FloatArray := Id.run do
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

def runKMeansBenchmarks : IO Unit := do
  let d := 64
  let n := 10000
  let k := 32

  IO.println s!"KMeans: n={n}, d={d}, k={k}"

  let points ← FloatArray.random (n * d)
  let centroids ← FloatArray.random (k * d)

  let config : Benchmark.Config := { warmupIterations := 2, timedIterations := 10 }
  let mut suite : Benchmark.Suite := { name := "KMeans Benchmark" }

  -- CPU
  let cpuResult ← Benchmark.run "CPU (naive loops)" config fun () => do
    let _ := kmeansCPU d n k points centroids
    pure ()
  suite := suite.add cpuResult

  -- GPU
  if Metal.isAvailable () then
    let gpuResult ← Benchmark.run "GPU (Metal)" config fun () => do
      let _ := Metal.kmeans d.toUSize n.toUSize k.toUSize points centroids
      pure ()
    suite := suite.add gpuResult

  suite.print

def runGEMMBenchmarks : IO Unit := do
  let m := 512
  let kk := 512
  let nn := 512

  IO.println s!"\nGEMM: {m}x{kk} @ {kk}x{nn}"

  let A ← FloatArray.random (m * kk)
  let B ← FloatArray.random (kk * nn)

  let cpuConfig : Benchmark.Config := { warmupIterations := 1, timedIterations := 3 }
  let gpuConfig : Benchmark.Config := { warmupIterations := 1, timedIterations := 10 }
  let mut suite : Benchmark.Suite := { name := "GEMM Benchmark" }

  -- CPU
  let cpuResult ← Benchmark.run "CPU (naive loops)" cpuConfig fun () => do
    let _ := gemmCPU m kk nn A B
    pure ()
  suite := suite.add cpuResult

  -- GPU
  if Metal.isAvailable () then
    let gpuResult ← Benchmark.run "GPU (Metal)" gpuConfig fun () => do
      let _ := Metal.gemm m.toUSize kk.toUSize nn.toUSize A B
      pure ()
    suite := suite.add gpuResult

  suite.print

def main : IO Unit := do
  IO.println "╔════════════════════════════════════════════════════════════╗"
  IO.println "║           SciLean Metal GPU Benchmark                      ║"
  IO.println "╚════════════════════════════════════════════════════════════╝"
  IO.println ""
  IO.println s!"Metal available: {Metal.isAvailable ()}"

  runKMeansBenchmarks
  runGEMMBenchmarks

  IO.println "\nBenchmark complete!"

end MetalBenchmark

def main := MetalBenchmark.main
