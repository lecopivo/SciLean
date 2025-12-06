import SciLean.FFI.Metal
import SciLean.FFI.Float32Array

open SciLean

def main : IO Unit := do
  IO.println "=== Metal Float32 FFI Verification ==="

  -- Verify ugetFloat32 works
  let arr := ByteArray.mk #[0x00, 0x00, 0x80, 0x3F]  -- 1.0f IEEE 754
  IO.println s!"ugetFloat32([0,0,128,63]) = {arr.ugetFloat32 0} (expected 1.0)"

  -- Verify Metal.Float32.fill works
  let filled := Metal.Float32.fill 4 (2.5 : Float32)
  IO.println s!"Metal.Float32.fill 4 2.5 = [{filled.ugetFloat32 0}, {filled.ugetFloat32 4}, {filled.ugetFloat32 8}, {filled.ugetFloat32 12}]"

  IO.println ""
  IO.println "=== Metal.Float32.add Verification ==="

  -- Create two arrays with known values
  let a := Metal.Float32.fill 4 (1.0 : Float32)
  let b := Metal.Float32.fill 4 (2.0 : Float32)
  let c := Metal.Float32.add 4 a b

  IO.println s!"a = [{a.ugetFloat32 0}, {a.ugetFloat32 4}, {a.ugetFloat32 8}, {a.ugetFloat32 12}]"
  IO.println s!"b = [{b.ugetFloat32 0}, {b.ugetFloat32 4}, {b.ugetFloat32 8}, {b.ugetFloat32 12}]"
  IO.println s!"a + b = [{c.ugetFloat32 0}, {c.ugetFloat32 4}, {c.ugetFloat32 8}, {c.ugetFloat32 12}] (expected [3,3,3,3])"

  IO.println ""
  IO.println "=== Metal.Float32.reduceSum Verification ==="

  let arr4 := Metal.Float32.fill 4 (1.0 : Float32)
  let sum4 := Metal.Float32.reduceSum 4 arr4
  IO.println s!"sum([1,1,1,1]) = {sum4} (expected 4.0)"

  IO.println ""
  IO.println "=== Metal Dispatch Overhead Measurement ==="
  IO.println "(Using result accumulation to prevent DCE)"

  -- Warmup
  for _ in [:10] do
    let _ := Metal.Float32.fill 1 (1.0 : Float32)

  -- Measure fill (n=1) - accumulate sizes to force evaluation
  let iters := 1000
  let fillStart ← IO.monoNanosNow
  let mut totalSize := 0
  for _ in [:iters] do
    let r := Metal.Float32.fill 1 (1.0 : Float32)
    totalSize := totalSize + r.size
  let fillEnd ← IO.monoNanosNow
  let fillOverhead := (fillEnd - fillStart) / iters
  IO.println s!"fill(n=1) overhead: {fillOverhead} ns/call (accumulated size: {totalSize})"

  -- Measure add (n=1)
  let a1 := Metal.Float32.fill 1 (1.0 : Float32)
  let b1 := Metal.Float32.fill 1 (1.0 : Float32)

  let addStart ← IO.monoNanosNow
  totalSize := 0
  for _ in [:iters] do
    let r := Metal.Float32.add 1 a1 b1
    totalSize := totalSize + r.size
  let addEnd ← IO.monoNanosNow
  let addOverhead := (addEnd - addStart) / iters
  IO.println s!"add(n=1) overhead: {addOverhead} ns/call (accumulated size: {totalSize})"

  -- Measure reduceSum (n=1) - accumulate float results
  let reduceStart ← IO.monoNanosNow
  let mut totalSum : Float32 := 0.0
  for _ in [:iters] do
    let r := Metal.Float32.reduceSum 1 a1
    totalSum := totalSum + r
  let reduceEnd ← IO.monoNanosNow
  let reduceOverhead := (reduceEnd - reduceStart) / iters
  IO.println s!"reduceSum(n=1) overhead: {reduceOverhead} ns/call (accumulated sum: {totalSum})"

  IO.println ""
  IO.println "=== Scaling with Size ==="

  -- Measure how overhead scales with size
  for size in [1, 10, 100, 1000, 10000, 100000] do
    let arr := Metal.Float32.fill size.toUSize (1.0 : Float32)
    let numIters := if size > 1000 then 100 else 1000

    let scaleStart ← IO.monoNanosNow
    let mut sumAccum : Float32 := 0.0
    for _ in [:numIters] do
      let r := Metal.Float32.reduceSum size.toUSize arr
      sumAccum := sumAccum + r
    let scaleEnd ← IO.monoNanosNow

    let nsPerCall := (scaleEnd - scaleStart) / numIters
    let elemPerSec := if nsPerCall > 0 then size.toFloat * 1e9 / nsPerCall.toFloat else 0.0
    let mElemPerSec := elemPerSec / 1e6
    IO.println s!"reduceSum(n={size}): {nsPerCall} ns/call, {mElemPerSec} M elem/s (sum={sumAccum})"

  IO.println ""
  IO.println "=== GEMM Scaling ==="

  for n in [32, 64, 128, 256, 512] do
    let amat := Metal.Float32.fill (n * n).toUSize (1.0 : Float32)
    let bmat := Metal.Float32.fill (n * n).toUSize (1.0 : Float32)
    let numIters := if n > 256 then 10 else 100

    let gemmStart ← IO.monoNanosNow
    let mut sizeAccum := 0
    for _ in [:numIters] do
      let r := Metal.Float32.gemm n.toUSize n.toUSize n.toUSize amat bmat
      sizeAccum := sizeAccum + r.size
    let gemmEnd ← IO.monoNanosNow

    let nsPerCall := (gemmEnd - gemmStart) / numIters
    let flops := 2.0 * n.toFloat * n.toFloat * n.toFloat
    let gflops := if nsPerCall > 0 then flops / nsPerCall.toFloat else 0.0
    let usPerCall := nsPerCall / 1000
    IO.println s!"gemm({n}×{n}): {usPerCall} µs, {gflops} GFLOP/s (size={sizeAccum})"
