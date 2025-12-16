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

def main : IO Unit := do
  if Metal.isAvailable () then
    IO.println "Metal GPU available, running tests...\n"
    testGemmBiasRelu
    testBatching
    testBiasRelu
    IO.println "\n=== All tests completed ==="
  else
    IO.println "Metal GPU not available, skipping tests"
