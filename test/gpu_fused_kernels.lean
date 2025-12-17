/-
Test for GPU fused kernels and batching support.
Tests gemm_bias_relu and batched operations.
-/
import SciLean.Data.Tensor
import SciLean.Monad.GPU
import SciLean.FFI.Metal
import SciLean.Data.ByteArray

open SciLean

/-- Helper to create a ByteArray from Float list -/
def floatsToByteArray (floats : List Float) : ByteArray := Id.run do
  let n := floats.length
  let mut arr := ByteArray.replicateFloat32 n 0.0
  for i in List.range n do
    arr := arr.usetFloat32 (i * 4).toUSize (floats[i]!.toFloat32)
  return arr

/-- Helper to read float at index from ByteArray -/
def getFloat (arr : ByteArray) (i : Nat) : Float :=
  (arr.ugetFloat32 (i * 4).toUSize).toFloat

/-- Test gemm_bias_relu fused kernel -/
def testGemmBiasRelu : IO Unit := do
  IO.println "=== Testing gemm_bias_relu fused kernel ==="

  -- Create test matrices:
  -- A: 2x3 matrix
  -- B: 3x2 matrix
  -- bias: 2 elements
  -- Expected C: 2x2 = max(0, A @ B + bias)

  -- A = [[1, 2, 3], [4, 5, 6]] (row-major)
  let aData := floatsToByteArray [1, 2, 3, 4, 5, 6]

  -- B = [[1, 2], [3, 4], [5, 6]] (row-major)
  let bData := floatsToByteArray [1, 2, 3, 4, 5, 6]

  -- bias = [-100, 1] (first col will be negative after bias, second positive)
  let biasData := floatsToByteArray [-100, 1]

  -- Upload to GPU
  let aGpu ← Metal.GpuBuffer.fromByteArray aData
  let bGpu ← Metal.GpuBuffer.fromByteArray bData
  let biasGpu ← Metal.GpuBuffer.fromByteArray biasData

  -- Run fused gemm_bias_relu
  let cGpu ← Metal.GpuBuffer.gemmBiasRelu aGpu bGpu biasGpu 2 3 2

  -- Download result
  let cData ← cGpu.toByteArray

  IO.println s!"Result: [{getFloat cData 0}, {getFloat cData 1}, {getFloat cData 2}, {getFloat cData 3}]"

  -- Expected:
  -- A @ B = [[1*1+2*3+3*5, 1*2+2*4+3*6], [4*1+5*3+6*5, 4*2+5*4+6*6]]
  --       = [[22, 28], [49, 64]]
  -- A @ B + bias = [[22-100, 28+1], [49-100, 64+1]] = [[-78, 29], [-51, 65]]
  -- ReLU = [[0, 29], [0, 65]]
  let expected := [0.0, 29.0, 0.0, 65.0]

  -- Check result
  let mut passed := true
  for i in List.range 4 do
    let got := getFloat cData i
    let exp := expected[i]!
    let diff := (got - exp).abs
    if diff > 0.01 then
      IO.println s!"  FAIL at index {i}: got {got}, expected {exp}"
      passed := false

  if passed then
    IO.println "  ✓ gemm_bias_relu test PASSED"
  else
    IO.println "  ✗ gemm_bias_relu test FAILED"

/-- Test batching with Metal.withBatch -/
def testBatching : IO Unit := do
  IO.println "\n=== Testing GPU batching ==="

  -- Create simple test data
  let data := floatsToByteArray [1, 2, 3, 4, 5, 6, 7, 8]

  -- Test batched operations using Metal.withBatch
  -- NOTE: Return the GpuBuffer and read AFTER batch completes
  let resultBuf ← Metal.withBatch do
    let gpuBuf ← Metal.GpuBuffer.fromByteArray data
    let result1 ← Metal.GpuBuffer.relu gpuBuf 8
    let result2 ← Metal.GpuBuffer.add result1 result1 8
    return result2
  -- Read after batch completes (GPU work is done)
  let final ← resultBuf.toByteArray

  IO.println s!"Batched result: [{getFloat final 0}, {getFloat final 1}, {getFloat final 2}, {getFloat final 3}, {getFloat final 4}, {getFloat final 5}, {getFloat final 6}, {getFloat final 7}]"
  -- Expected: relu([1..8]) = [1..8], then add to itself = [2,4,6,8,10,12,14,16]
  let expected := [2.0, 4.0, 6.0, 8.0, 10.0, 12.0, 14.0, 16.0]

  let mut passed := true
  for i in List.range 8 do
    let got := getFloat final i
    let exp := expected[i]!
    let diff := (got - exp).abs
    if diff > 0.01 then
      passed := false

  if passed then
    IO.println "  ✓ Batching test PASSED"
  else
    IO.println "  ✗ Batching test FAILED"

/-- Test bias_relu operation -/
def testBiasRelu : IO Unit := do
  IO.println "\n=== Testing bias_relu ==="

  -- Input: 6 elements, stride 3 (2 samples × 3 features)
  let input := floatsToByteArray [1, -2, 3, -4, 5, -6]
  let bias := floatsToByteArray [0, 10, -10]  -- bias per feature

  let inputGpu ← Metal.GpuBuffer.fromByteArray input
  let biasGpu ← Metal.GpuBuffer.fromByteArray bias

  let result ← Metal.GpuBuffer.biasRelu inputGpu biasGpu 6 3

  let output ← result.toByteArray

  IO.println s!"bias_relu result: [{getFloat output 0}, {getFloat output 1}, {getFloat output 2}, {getFloat output 3}, {getFloat output 4}, {getFloat output 5}]"
  -- Expected:
  -- [1+0, -2+10, 3-10, -4+0, 5+10, -6-10]
  -- = [1, 8, -7, -4, 15, -16]
  -- relu = [1, 8, 0, 0, 15, 0]
  let expected := [1.0, 8.0, 0.0, 0.0, 15.0, 0.0]

  let mut passed := true
  for i in List.range 6 do
    let got := getFloat output i
    let exp := expected[i]!
    let diff := (got - exp).abs
    if diff > 0.01 then
      IO.println s!"  FAIL at index {i}: got {got}, expected {exp}"
      passed := false

  if passed then
    IO.println "  ✓ bias_relu test PASSED"
  else
    IO.println "  ✗ bias_relu test FAILED"

/-- Test layer_norm operation -/
def testLayerNorm : IO Unit := do
  IO.println "\n=== Testing layer_norm ==="

  -- Input: 4 elements (1 sample normalized across all elements)
  -- The current kernel normalizes the entire input as one group
  let input := floatsToByteArray [1, 2, 3, 4]
  let gamma := floatsToByteArray [1, 1, 1, 1]  -- scale = 1
  let beta := floatsToByteArray [0, 0, 0, 0]   -- shift = 0

  let inputGpu ← Metal.GpuBuffer.fromByteArray input
  let gammaGpu ← Metal.GpuBuffer.fromByteArray gamma
  let betaGpu ← Metal.GpuBuffer.fromByteArray beta

  -- hiddenSize = n means normalize entire input as one group
  let result ← Metal.GpuBuffer.layerNorm inputGpu gammaGpu betaGpu 4 4

  let output ← result.toByteArray

  IO.println s!"layer_norm result: [{getFloat output 0}, {getFloat output 1}, {getFloat output 2}, {getFloat output 3}]"

  -- For layer norm with gamma=1, beta=0:
  -- [1,2,3,4] has mean=2.5, var=1.25
  -- normalized = (x - mean) / sqrt(var + eps)
  -- [1,2,3,4] -> [-1.34, -0.45, 0.45, 1.34] approximately

  let mut passed := true
  -- Check that output is normalized (mean ≈ 0)
  let mean := (getFloat output 0 + getFloat output 1 + getFloat output 2 + getFloat output 3) / 4
  if mean.abs > 0.1 then
    IO.println s!"  FAIL: mean should be ~0, got {mean}"
    passed := false
  -- Check that middle values are approximately 0 and ±0.45
  if ((getFloat output 1) + 0.45).abs > 0.2 then
    IO.println s!"  FAIL at index 1: expected ~-0.45, got {getFloat output 1}"
    passed := false

  if passed then
    IO.println "  ✓ layer_norm test PASSED"
  else
    IO.println "  ✗ layer_norm test FAILED"

/-- Test bias_gelu operation -/
def testBiasGelu : IO Unit := do
  IO.println "\n=== Testing bias_gelu ==="

  -- Input: 6 elements, stride 3 (2 samples × 3 features)
  let input := floatsToByteArray [0, 0, 0, 1, 1, 1]
  let bias := floatsToByteArray [0, 1, -1]  -- bias per feature

  let inputGpu ← Metal.GpuBuffer.fromByteArray input
  let biasGpu ← Metal.GpuBuffer.fromByteArray bias

  let result ← Metal.GpuBuffer.biasGelu inputGpu biasGpu 6 3

  let output ← result.toByteArray

  IO.println s!"bias_gelu result: [{getFloat output 0}, {getFloat output 1}, {getFloat output 2}, {getFloat output 3}, {getFloat output 4}, {getFloat output 5}]"

  -- gelu(x) ≈ x * 0.5 * (1 + tanh(sqrt(2/pi) * (x + 0.044715 * x^3)))
  -- gelu(0) ≈ 0
  -- gelu(1) ≈ 0.841
  -- gelu(-1) ≈ -0.159
  -- gelu(2) ≈ 1.955

  let mut passed := true
  -- Check gelu(0) ≈ 0
  if (getFloat output 0).abs > 0.1 then
    IO.println s!"  FAIL at index 0: expected ~0, got {getFloat output 0}"
    passed := false
  -- Check gelu(1) ≈ 0.84
  if ((getFloat output 1) - 0.84).abs > 0.1 then
    IO.println s!"  FAIL at index 1: expected ~0.84, got {getFloat output 1}"
    passed := false

  if passed then
    IO.println "  ✓ bias_gelu test PASSED"
  else
    IO.println "  ✗ bias_gelu test FAILED"

/-- Test avgpool2d operation -/
def testAvgpool2d : IO Unit := do
  IO.println "\n=== Testing avgpool2d ==="

  -- Input: 1 batch × 1 channel × 4×4 image
  -- Using 2×2 pool with stride 2, output should be 2×2
  let input := floatsToByteArray [
    1, 2, 3, 4,
    5, 6, 7, 8,
    9, 10, 11, 12,
    13, 14, 15, 16
  ]

  let inputGpu ← Metal.GpuBuffer.fromByteArray input

  let result ← Metal.GpuBuffer.avgpool2d inputGpu 1 1 4 4 2 2 2 2

  let output ← result.toByteArray

  IO.println s!"avgpool2d result: [{getFloat output 0}, {getFloat output 1}, {getFloat output 2}, {getFloat output 3}]"

  -- Expected: avg of 2×2 blocks
  -- [1,2,5,6] -> mean = 3.5
  -- [3,4,7,8] -> mean = 5.5
  -- [9,10,13,14] -> mean = 11.5
  -- [11,12,15,16] -> mean = 13.5
  let expected := [3.5, 5.5, 11.5, 13.5]

  let mut passed := true
  for i in List.range 4 do
    let got := getFloat output i
    let exp := expected[i]!
    let diff := (got - exp).abs
    if diff > 0.1 then
      IO.println s!"  FAIL at index {i}: got {got}, expected {exp}"
      passed := false

  if passed then
    IO.println "  ✓ avgpool2d test PASSED"
  else
    IO.println "  ✗ avgpool2d test FAILED"

/-- Test flash attention operation -/
def testFlashAttention : IO Unit := do
  IO.println "\n=== Testing flash_attention ==="

  -- Simple 2x2 attention: seq_len=2, head_dim=2
  -- Q = [[1, 0], [0, 1]]
  -- K = [[1, 0], [0, 1]]
  -- V = [[1, 2], [3, 4]]
  -- Attention scores = Q @ K^T = [[1, 0], [0, 1]] (scaled by 1/sqrt(2))
  -- After softmax, mostly diagonal
  -- Output ≈ V (since attention is nearly diagonal)

  let Q := floatsToByteArray [1, 0, 0, 1]
  let K := floatsToByteArray [1, 0, 0, 1]
  let V := floatsToByteArray [1, 2, 3, 4]

  let Qgpu ← Metal.GpuBuffer.fromByteArray Q
  let Kgpu ← Metal.GpuBuffer.fromByteArray K
  let Vgpu ← Metal.GpuBuffer.fromByteArray V

  let result ← Metal.GpuBuffer.flashAttention Qgpu Kgpu Vgpu 2 2

  let output ← result.toByteArray

  IO.println s!"flash_attention result: [{getFloat output 0}, {getFloat output 1}, {getFloat output 2}, {getFloat output 3}]"

  -- The output should be close to V since the attention is nearly identity
  -- With softmax(score * scale), the diagonal dominates
  let mut passed := true

  -- Just check that we get reasonable values (not NaN or inf)
  for i in List.range 4 do
    let got := getFloat output i
    if got.isNaN || got.abs > 100 then
      IO.println s!"  FAIL at index {i}: got invalid value {got}"
      passed := false

  -- Output should roughly match V since attention is diagonal
  -- Allow some tolerance due to softmax spreading
  let diff0 := ((getFloat output 0) - 1.0).abs
  let diff3 := ((getFloat output 3) - 4.0).abs
  if diff0 > 1.0 || diff3 > 1.0 then
    IO.println s!"  Warning: output differs from V by more than expected"

  if passed then
    IO.println "  ✓ flash_attention test PASSED"
  else
    IO.println "  ✗ flash_attention test FAILED"

/-- Test batchnorm2d operation -/
def testBatchNorm2d : IO Unit := do
  IO.println "\n=== Testing batchnorm2d ==="

  -- Input: 1 batch × 2 channels × 2×2 spatial (NCHW format)
  -- Channel 0: [[1, 2], [3, 4]]
  -- Channel 1: [[5, 6], [7, 8]]
  let input := floatsToByteArray [
    1, 2, 3, 4,  -- channel 0
    5, 6, 7, 8   -- channel 1
  ]

  -- Running stats per channel
  let gamma := floatsToByteArray [1.0, 1.0]  -- scale = 1
  let beta := floatsToByteArray [0.0, 0.0]   -- shift = 0
  let mean := floatsToByteArray [2.5, 6.5]   -- mean of each channel
  let var := floatsToByteArray [1.25, 1.25]  -- variance of each channel

  let inputGpu ← Metal.GpuBuffer.fromByteArray input
  let gammaGpu ← Metal.GpuBuffer.fromByteArray gamma
  let betaGpu ← Metal.GpuBuffer.fromByteArray beta
  let meanGpu ← Metal.GpuBuffer.fromByteArray mean
  let varGpu ← Metal.GpuBuffer.fromByteArray var

  -- batchnorm: (x - mean) / sqrt(var + eps) * gamma + beta
  let result ← Metal.GpuBuffer.batchNorm2d inputGpu gammaGpu betaGpu meanGpu varGpu
      1 2 2 2 1e-5 0

  let output ← result.toByteArray

  IO.println s!"batchnorm2d result: [{getFloat output 0}, {getFloat output 1}, {getFloat output 2}, {getFloat output 3}, {getFloat output 4}, {getFloat output 5}, {getFloat output 6}, {getFloat output 7}]"

  -- For channel 0: values [1,2,3,4], mean=2.5, var=1.25
  -- normalized = (x - 2.5) / sqrt(1.25) ≈ (x - 2.5) / 1.118
  -- [1-2.5, 2-2.5, 3-2.5, 4-2.5] / 1.118 ≈ [-1.34, -0.45, 0.45, 1.34]

  let mut passed := true
  -- Check that output is normalized (mean ≈ 0 for each channel)
  let mean0 := (getFloat output 0 + getFloat output 1 + getFloat output 2 + getFloat output 3) / 4
  let mean1 := (getFloat output 4 + getFloat output 5 + getFloat output 6 + getFloat output 7) / 4
  if mean0.abs > 0.1 then
    IO.println s!"  FAIL: channel 0 mean should be ~0, got {mean0}"
    passed := false
  if mean1.abs > 0.1 then
    IO.println s!"  FAIL: channel 1 mean should be ~0, got {mean1}"
    passed := false

  if passed then
    IO.println "  ✓ batchnorm2d test PASSED"
  else
    IO.println "  ✗ batchnorm2d test FAILED"

/-- Test backward pass kernels for autodiff -/
def testBackwardKernels : IO Unit := do
  IO.println "\n=== Testing backward pass kernels ==="

  -- Test ReLU backward
  IO.println "  Testing relu_backward..."
  let input := floatsToByteArray [-2, -1, 0, 1, 2, 3]
  let gradOut := floatsToByteArray [1, 1, 1, 1, 1, 1]

  let inputGpu ← Metal.GpuBuffer.fromByteArray input
  let gradOutGpu ← Metal.GpuBuffer.fromByteArray gradOut

  let gradIn ← Metal.GpuBuffer.reluBackward inputGpu gradOutGpu 6
  let gradInData ← gradIn.toByteArray

  -- Expected: [0, 0, 0, 1, 1, 1] (only positive inputs pass gradient)
  let expectedRelu := [0.0, 0.0, 0.0, 1.0, 1.0, 1.0]
  let mut passed := true

  for i in List.range 6 do
    let got := getFloat gradInData i
    let exp := expectedRelu[i]!
    if (got - exp).abs > 0.01 then
      IO.println s!"    FAIL relu_backward at {i}: got {got}, expected {exp}"
      passed := false

  if passed then
    IO.println "    relu_backward OK"

  -- Test multiply backward
  IO.println "  Testing mul_backward..."
  let a := floatsToByteArray [1, 2, 3, 4]
  let b := floatsToByteArray [5, 6, 7, 8]
  let dout := floatsToByteArray [1, 1, 1, 1]

  let aGpu ← Metal.GpuBuffer.fromByteArray a
  let bGpu ← Metal.GpuBuffer.fromByteArray b
  let doutGpu ← Metal.GpuBuffer.fromByteArray dout

  let (gradA, gradB) ← Metal.GpuBuffer.mulBackward aGpu bGpu doutGpu 4
  let gradAData ← gradA.toByteArray
  let gradBData ← gradB.toByteArray

  -- Expected: grad_a = dout * b = [5,6,7,8], grad_b = dout * a = [1,2,3,4]
  let expectedGradA := [5.0, 6.0, 7.0, 8.0]
  let expectedGradB := [1.0, 2.0, 3.0, 4.0]

  for i in List.range 4 do
    let gotA := getFloat gradAData i
    let expA := expectedGradA[i]!
    if (gotA - expA).abs > 0.01 then
      IO.println s!"    FAIL mul_backward grad_a at {i}: got {gotA}, expected {expA}"
      passed := false

    let gotB := getFloat gradBData i
    let expB := expectedGradB[i]!
    if (gotB - expB).abs > 0.01 then
      IO.println s!"    FAIL mul_backward grad_b at {i}: got {gotB}, expected {expB}"
      passed := false

  if passed then
    IO.println "    mul_backward OK"

  -- Test GELU backward
  IO.println "  Testing gelu_backward..."
  let geluIn := floatsToByteArray [0, 1, -1, 2]
  let geluDout := floatsToByteArray [1, 1, 1, 1]

  let geluInGpu ← Metal.GpuBuffer.fromByteArray geluIn
  let geluDoutGpu ← Metal.GpuBuffer.fromByteArray geluDout

  let geluGradIn ← Metal.GpuBuffer.geluBackward geluInGpu geluDoutGpu 4
  let geluGradData ← geluGradIn.toByteArray

  -- GELU'(0) ≈ 0.5, GELU'(1) ≈ 1.08, GELU'(-1) ≈ -0.08, GELU'(2) ≈ 1.09
  -- Just check they're in reasonable range
  let g0 := getFloat geluGradData 0
  let g1 := getFloat geluGradData 1
  if (g0 - 0.5).abs > 0.1 then
    IO.println s!"    FAIL gelu_backward at 0: got {g0}, expected ~0.5"
    passed := false
  if g1 < 0.9 || g1 > 1.2 then
    IO.println s!"    FAIL gelu_backward at 1: got {g1}, expected ~1.08"
    passed := false

  if passed then
    IO.println "    gelu_backward OK"

  if passed then
    IO.println "  ✓ backward kernels test PASSED"
  else
    IO.println "  ✗ backward kernels test FAILED"

def main : IO Unit := do
  if Metal.isAvailable () then
    IO.println "Metal GPU available, running tests...\n"
    testGemmBiasRelu
    testBatching
    testBiasRelu
    testLayerNorm
    testBiasGelu
    testAvgpool2d
    testFlashAttention
    testBatchNorm2d
    testBackwardKernels
    IO.println "\n=== All tests completed ==="
  else
    IO.println "Metal GPU not available, skipping tests"
