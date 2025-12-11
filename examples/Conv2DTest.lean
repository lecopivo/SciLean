-- Test Conv2D Metal kernels
import SciLean.FFI.Metal
import SciLean.FFI.Float32Array

open SciLean

-- Generate Float32 test data
def generateFloat32Data (n : Nat) (offset : Float := 0.0) : ByteArray := Id.run do
  let mut arr := ByteArray.empty
  for _ in [:n * 4] do
    arr := arr.push 0
  for i in [:n] do
    let v : Float32 := Float.toFloat32 (i.toFloat * 0.01 + offset)
    arr := arr.usetFloat32 (i * 4).toUSize v
  return arr

-- Generate constant array
def constantFloat32 (n : Nat) (value : Float32) : ByteArray := Id.run do
  let mut arr := ByteArray.empty
  for _ in [:n * 4] do
    arr := arr.push 0
  for i in [:n] do
    arr := arr.usetFloat32 (i * 4).toUSize value
  return arr

-- CPU reference for Conv2D (NCHW format)
def cpuConv2d (batchSize inChannels outChannels : Nat)
    (inHeight inWidth : Nat)
    (kernelH kernelW : Nat)
    (strideH strideW : Nat)
    (padH padW : Nat)
    (input kernel bias : ByteArray) : ByteArray := Id.run do
  let outHeight := (inHeight + 2 * padH - kernelH) / strideH + 1
  let outWidth := (inWidth + 2 * padW - kernelW) / strideW + 1
  let outSize := batchSize * outChannels * outHeight * outWidth
  let mut output := ByteArray.empty
  for _ in [:outSize * 4] do
    output := output.push 0

  for batch in [:batchSize] do
    for oc in [:outChannels] do
      for oh in [:outHeight] do
        for ow in [:outWidth] do
          let biasIdx := oc * 4
          let mut sum := bias.ugetFloat32 biasIdx.toUSize

          for ic in [:inChannels] do
            for kh in [:kernelH] do
              for kw in [:kernelW] do
                let ih : Int := oh * strideH + kh - padH
                let iw : Int := ow * strideW + kw - padW

                if ih >= 0 && ih < inHeight && iw >= 0 && iw < inWidth then
                  let inIdx := batch * inChannels * inHeight * inWidth
                            + ic * inHeight * inWidth
                            + ih.toNat * inWidth + iw.toNat
                  let kIdx := oc * inChannels * kernelH * kernelW
                            + ic * kernelH * kernelW
                            + kh * kernelW + kw
                  let inVal := input.ugetFloat32 (inIdx * 4).toUSize
                  let kVal := kernel.ugetFloat32 (kIdx * 4).toUSize
                  sum := sum + inVal * kVal

          let outIdx := batch * outChannels * outHeight * outWidth
                      + oc * outHeight * outWidth
                      + oh * outWidth + ow
          output := output.usetFloat32 (outIdx * 4).toUSize sum

  return output

-- CPU reference for MaxPool2D
def cpuMaxPool2d (batchSize channels : Nat)
    (inHeight inWidth : Nat)
    (poolH poolW : Nat)
    (strideH strideW : Nat)
    (input : ByteArray) : ByteArray := Id.run do
  let outHeight := (inHeight - poolH) / strideH + 1
  let outWidth := (inWidth - poolW) / strideW + 1
  let outSize := batchSize * channels * outHeight * outWidth
  let mut output := ByteArray.empty
  for _ in [:outSize * 4] do
    output := output.push 0

  for batch in [:batchSize] do
    for c in [:channels] do
      for oh in [:outHeight] do
        for ow in [:outWidth] do
          let mut maxVal : Float32 := -1e30

          for ph in [:poolH] do
            for pw in [:poolW] do
              let ih := oh * strideH + ph
              let iw := ow * strideW + pw
              let inIdx := batch * channels * inHeight * inWidth
                        + c * inHeight * inWidth
                        + ih * inWidth + iw
              let val := input.ugetFloat32 (inIdx * 4).toUSize
              if val > maxVal then
                maxVal := val

          let outIdx := batch * channels * outHeight * outWidth
                      + c * outHeight * outWidth
                      + oh * outWidth + ow
          output := output.usetFloat32 (outIdx * 4).toUSize maxVal

  return output

-- Compare arrays and compute max error
def maxError (a b : ByteArray) : Float32 := Id.run do
  let n := min a.size b.size / 4
  let mut maxErr : Float32 := 0
  for i in [:n] do
    let va := a.ugetFloat32 (i * 4).toUSize
    let vb := b.ugetFloat32 (i * 4).toUSize
    let err := Float32.abs (va - vb)
    if err > maxErr then
      maxErr := err
  return maxErr

def main : IO Unit := do
  IO.println "╔═══════════════════════════════════════════════════════════╗"
  IO.println "║          Conv2D Metal Kernel Test                         ║"
  IO.println "╚═══════════════════════════════════════════════════════════╝"

  if !Metal.isAvailable () then
    IO.println "\nMetal GPU: Not available"
    return

  IO.println "\nMetal GPU: Available"
  IO.println ""

  -- Test 1: Simple Conv2D 3x3 kernel
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "Test 1: Conv2D 3x3 kernel, 1 input channel, 1 output channel"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  let batchSize := 1
  let inChannels := 1
  let outChannels := 1
  let inHeight := 8
  let inWidth := 8
  let kernelH := 3
  let kernelW := 3
  let strideH := 1
  let strideW := 1
  let padH := 0
  let padW := 0

  let input1 := generateFloat32Data (batchSize * inChannels * inHeight * inWidth)
  let kernel1 := constantFloat32 (outChannels * inChannels * kernelH * kernelW) 1.0
  let bias1 := constantFloat32 outChannels 0.0

  let cpuOut1 := cpuConv2d batchSize inChannels outChannels inHeight inWidth
                           kernelH kernelW strideH strideW padH padW input1 kernel1 bias1

  let gpuOut1 := Metal.Float32.conv2d batchSize.toUSize inChannels.toUSize outChannels.toUSize
                                      inHeight.toUSize inWidth.toUSize
                                      kernelH.toUSize kernelW.toUSize
                                      strideH.toUSize strideW.toUSize
                                      padH.toUSize padW.toUSize
                                      0 -- no ReLU
                                      input1 kernel1 bias1

  let err1 := maxError cpuOut1 gpuOut1
  IO.println s!"  Max error: {Float32.toFloat err1}"
  IO.println s!"  Status: {if err1 < 0.001 then "PASS ✓" else "FAIL ✗"}"
  IO.println ""

  -- Test 2: Conv2D with padding
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "Test 2: Conv2D 3x3 with padding=1 (same output size)"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  let padH2 := 1
  let padW2 := 1

  let cpuOut2 := cpuConv2d batchSize inChannels outChannels inHeight inWidth
                           kernelH kernelW strideH strideW padH2 padW2 input1 kernel1 bias1

  let gpuOut2 := Metal.Float32.conv2d batchSize.toUSize inChannels.toUSize outChannels.toUSize
                                      inHeight.toUSize inWidth.toUSize
                                      kernelH.toUSize kernelW.toUSize
                                      strideH.toUSize strideW.toUSize
                                      padH2.toUSize padW2.toUSize
                                      0 input1 kernel1 bias1

  let err2 := maxError cpuOut2 gpuOut2
  IO.println s!"  Max error: {Float32.toFloat err2}"
  IO.println s!"  Status: {if err2 < 0.001 then "PASS ✓" else "FAIL ✗"}"
  IO.println ""

  -- Test 3: Multi-channel Conv2D
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "Test 3: Conv2D 3 input channels -> 8 output channels"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  let inChannels3 := 3
  let outChannels3 := 8
  let inHeight3 := 16
  let inWidth3 := 16

  let input3 := generateFloat32Data (batchSize * inChannels3 * inHeight3 * inWidth3)
  let kernel3 := generateFloat32Data (outChannels3 * inChannels3 * kernelH * kernelW) 0.1
  let bias3 := generateFloat32Data outChannels3 0.05

  let cpuOut3 := cpuConv2d batchSize inChannels3 outChannels3 inHeight3 inWidth3
                           kernelH kernelW strideH strideW padH padW input3 kernel3 bias3

  let gpuOut3 := Metal.Float32.conv2d batchSize.toUSize inChannels3.toUSize outChannels3.toUSize
                                      inHeight3.toUSize inWidth3.toUSize
                                      kernelH.toUSize kernelW.toUSize
                                      strideH.toUSize strideW.toUSize
                                      padH.toUSize padW.toUSize
                                      0 input3 kernel3 bias3

  let err3 := maxError cpuOut3 gpuOut3
  IO.println s!"  Max error: {Float32.toFloat err3}"
  IO.println s!"  Status: {if err3 < 0.01 then "PASS ✓" else "FAIL ✗"}"
  IO.println ""

  -- Test 4: MaxPool2D
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "Test 4: MaxPool2D 2x2, stride 2"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  let poolChannels := 4
  let poolInH := 8
  let poolInW := 8
  let poolH := 2
  let poolW := 2
  let poolStrideH := 2
  let poolStrideW := 2

  let poolInput := generateFloat32Data (batchSize * poolChannels * poolInH * poolInW)

  let cpuPool := cpuMaxPool2d batchSize poolChannels poolInH poolInW
                              poolH poolW poolStrideH poolStrideW poolInput

  let gpuPool := Metal.Float32.maxPool2d batchSize.toUSize poolChannels.toUSize
                                         poolInH.toUSize poolInW.toUSize
                                         poolH.toUSize poolW.toUSize
                                         poolStrideH.toUSize poolStrideW.toUSize
                                         poolInput

  let errPool := maxError cpuPool gpuPool
  IO.println s!"  Max error: {Float32.toFloat errPool}"
  IO.println s!"  Status: {if errPool < 0.001 then "PASS ✓" else "FAIL ✗"}"
  IO.println ""

  -- Test 5: Global Average Pool
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "Test 5: Global Average Pooling"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  let gapChannels := 8
  let gapH := 4
  let gapW := 4
  let gapInput := constantFloat32 (batchSize * gapChannels * gapH * gapW) 2.0

  let gpuGap := Metal.Float32.globalAvgPool2d batchSize.toUSize gapChannels.toUSize
                                              gapH.toUSize gapW.toUSize gapInput

  -- Expected: all 2.0 since input is constant
  let mut gapOk := true
  for i in [:gapChannels] do
    let v := gpuGap.ugetFloat32 (i * 4).toUSize
    if Float32.abs (v - 2.0) > 0.001 then
      gapOk := false
      IO.println s!"  Channel {i}: expected 2.0, got {Float32.toFloat v}"

  IO.println s!"  Status: {if gapOk then "PASS ✓" else "FAIL ✗"}"
  IO.println ""

  -- Benchmark
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "BENCHMARK: Conv2D Performance (Naive vs Fast vs GEMM)"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  for (h, w, ic, oc) in [(28, 28, 1, 32), (28, 28, 32, 64), (14, 14, 64, 128), (224, 224, 3, 64)] do
    let benchInput := generateFloat32Data (1 * ic * h * w)
    let benchKernel := generateFloat32Data (oc * ic * 3 * 3)
    let benchBias := constantFloat32 oc 0.0

    -- Warmup naive
    for _ in [:3] do
      let _ := Metal.Float32.conv2d 1 ic.toUSize oc.toUSize
                                    h.toUSize w.toUSize
                                    3 3 1 1 1 1 0
                                    benchInput benchKernel benchBias

    -- Timed naive
    let iters := 100
    let acc ← IO.mkRef (0 : Nat)
    let start ← IO.monoNanosNow
    for _ in [:iters] do
      let out := Metal.Float32.conv2d 1 ic.toUSize oc.toUSize
                                      h.toUSize w.toUSize
                                      3 3 1 1 1 1 0
                                      benchInput benchKernel benchBias
      acc.modify (· + out.size)
    let stop ← IO.monoNanosNow
    let _ ← acc.get
    let msNaive := (stop - start).toFloat / 1000000.0 / iters.toFloat

    -- Warmup fast
    for _ in [:3] do
      let _ := Metal.Float32.conv2dFast 1 ic.toUSize oc.toUSize
                                        h.toUSize w.toUSize
                                        3 3 1 1 1 1 0
                                        benchInput benchKernel benchBias

    -- Timed fast
    let acc2 ← IO.mkRef (0 : Nat)
    let start2 ← IO.monoNanosNow
    for _ in [:iters] do
      let out := Metal.Float32.conv2dFast 1 ic.toUSize oc.toUSize
                                          h.toUSize w.toUSize
                                          3 3 1 1 1 1 0
                                          benchInput benchKernel benchBias
      acc2.modify (· + out.size)
    let stop2 ← IO.monoNanosNow
    let _ ← acc2.get
    let msFast := (stop2 - start2).toFloat / 1000000.0 / iters.toFloat

    -- Warmup GEMM
    for _ in [:3] do
      let _ := Metal.Float32.conv2dGemm 1 ic.toUSize oc.toUSize
                                        h.toUSize w.toUSize
                                        3 3 1 1 1 1 0
                                        benchInput benchKernel benchBias

    -- Timed GEMM
    let acc3 ← IO.mkRef (0 : Nat)
    let start3 ← IO.monoNanosNow
    for _ in [:iters] do
      let out := Metal.Float32.conv2dGemm 1 ic.toUSize oc.toUSize
                                          h.toUSize w.toUSize
                                          3 3 1 1 1 1 0
                                          benchInput benchKernel benchBias
      acc3.modify (· + out.size)
    let stop3 ← IO.monoNanosNow
    let _ ← acc3.get
    let msGemm := (stop3 - start3).toFloat / 1000000.0 / iters.toFloat

    -- FLOPS: 2 * outH * outW * outC * inC * kH * kW
    let outH := h  -- same padding
    let outW := w
    let flops := 2.0 * outH.toFloat * outW.toFloat * oc.toFloat * ic.toFloat * 9.0
    let gflopsNaive := if msNaive > 0.001 then flops / (msNaive / 1000.0) / 1e9 else 0.0
    let gflopsFast := if msFast > 0.001 then flops / (msFast / 1000.0) / 1e9 else 0.0
    let gflopsGemm := if msGemm > 0.001 then flops / (msGemm / 1000.0) / 1e9 else 0.0

    IO.println s!"  {h}x{w} x{ic}→{oc}:"
    IO.println s!"    Naive: {msNaive.toString.take 7}ms ({gflopsNaive.toString.take 5} GFLOP/s)"
    IO.println s!"    Fast:  {msFast.toString.take 7}ms ({gflopsFast.toString.take 5} GFLOP/s)"
    IO.println s!"    GEMM:  {msGemm.toString.take 7}ms ({gflopsGemm.toString.take 5} GFLOP/s)"

  IO.println ""
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "Test complete!"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
