/-
Attention Kernel Test

Tests the fused Flash Attention implementation on Metal GPU.
Verifies correctness against a naive CPU implementation.
-/
import SciLean.FFI.Metal
import SciLean.FFI.Float32Array

open SciLean

-- Helper: Create a ByteArray filled with Float32 values (using Metal.Float32.fill)
def fillFloat32 (n : Nat) (v : Float32) : ByteArray :=
  Metal.Float32.fill n.toUSize v

-- Helper: Create a ByteArray with sequential Float32 values (0, 1, 2, ...)
def sequentialFloat32 (n : Nat) : ByteArray := Id.run do
  let mut arr := ByteArray.replicateFloat32 n 0.0
  for i in [0:n] do
    let f : Float32 := i.toFloat.toFloat32
    arr := arr.usetFloat32 (i * 4).toUSize f
  arr

-- Helper: Create random-ish Float32 values (deterministic pseudo-random)
def pseudoRandomFloat32 (n : Nat) (seed : Nat := 42) : ByteArray := Id.run do
  let mut arr := ByteArray.replicateFloat32 n 0.0
  let mut x := seed
  for i in [0:n] do
    x := (x * 1103515245 + 12345) % (2^31)
    let f : Float32 := ((x % 1000).toFloat / 500.0 - 1.0).toFloat32  -- Range [-1, 1]
    arr := arr.usetFloat32 (i * 4).toUSize f
  arr

-- Helper: Read Float32 at index from ByteArray
def getFloat32 (arr : ByteArray) (i : Nat) : Float32 :=
  arr.ugetFloat32 (i * 4).toUSize

-- Helper: Set Float32 at index in ByteArray
def setFloat32 (arr : ByteArray) (i : Nat) (v : Float32) : ByteArray :=
  arr.usetFloat32 (i * 4).toUSize v

-- Helper: Compute sum of Float32 array
def sumFloat32 (arr : ByteArray) (n : Nat) : Float := Id.run do
  let mut sum : Float := 0.0
  for i in [0:n] do
    sum := sum + (getFloat32 arr i).toFloat
  sum

-- CPU reference implementation of single-head attention
-- Q, K, V: [seq_len, head_dim]
-- Returns: [seq_len, head_dim]
def cpuAttention (seqLen headDim : Nat) (Q K V : ByteArray) : ByteArray := Id.run do
  let scale := 1.0 / Float.sqrt headDim.toFloat
  let n := seqLen * headDim
  let mut output := ByteArray.replicateFloat32 n 0.0

  for q in [0:seqLen] do
    -- Compute attention scores for query q
    let mut maxScore : Float := -1e38
    for k in [0:seqLen] do
      let mut score : Float := 0.0
      for d in [0:headDim] do
        let qVal := (getFloat32 Q (q * headDim + d)).toFloat
        let kVal := (getFloat32 K (k * headDim + d)).toFloat
        score := score + qVal * kVal
      score := score * scale
      maxScore := if score > maxScore then score else maxScore

    -- Compute softmax denominator
    let mut sumExp : Float := 0.0
    for k in [0:seqLen] do
      let mut score : Float := 0.0
      for d in [0:headDim] do
        let qVal := (getFloat32 Q (q * headDim + d)).toFloat
        let kVal := (getFloat32 K (k * headDim + d)).toFloat
        score := score + qVal * kVal
      score := score * scale
      sumExp := sumExp + Float.exp (score - maxScore)

    -- Compute output for each dimension
    for d in [0:headDim] do
      let mut outVal : Float := 0.0
      for k in [0:seqLen] do
        -- Recompute attention weight
        let mut score : Float := 0.0
        for dd in [0:headDim] do
          let qVal := (getFloat32 Q (q * headDim + dd)).toFloat
          let kVal := (getFloat32 K (k * headDim + dd)).toFloat
          score := score + qVal * kVal
        score := score * scale
        let weight := Float.exp (score - maxScore) / sumExp
        let vVal := (getFloat32 V (k * headDim + d)).toFloat
        outVal := outVal + weight * vVal
      output := setFloat32 output (q * headDim + d) outVal.toFloat32

  output

-- CPU reference implementation of causal (masked) attention
-- Only attends to positions <= current position
def cpuAttentionCausal (seqLen headDim : Nat) (Q K V : ByteArray) : ByteArray := Id.run do
  let scale := 1.0 / Float.sqrt headDim.toFloat
  let n := seqLen * headDim
  let mut output := ByteArray.replicateFloat32 n 0.0

  for q in [0:seqLen] do
    -- Compute attention scores for query q (only for k <= q)
    let mut maxScore : Float := -1e38
    for k in [0:q+1] do  -- Causal mask: only positions 0..q
      let mut score : Float := 0.0
      for d in [0:headDim] do
        let qVal := (getFloat32 Q (q * headDim + d)).toFloat
        let kVal := (getFloat32 K (k * headDim + d)).toFloat
        score := score + qVal * kVal
      score := score * scale
      maxScore := if score > maxScore then score else maxScore

    -- Compute softmax denominator (only for k <= q)
    let mut sumExp : Float := 0.0
    for k in [0:q+1] do
      let mut score : Float := 0.0
      for d in [0:headDim] do
        let qVal := (getFloat32 Q (q * headDim + d)).toFloat
        let kVal := (getFloat32 K (k * headDim + d)).toFloat
        score := score + qVal * kVal
      score := score * scale
      sumExp := sumExp + Float.exp (score - maxScore)

    -- Compute output for each dimension (only considering k <= q)
    for d in [0:headDim] do
      let mut outVal : Float := 0.0
      for k in [0:q+1] do
        -- Recompute attention weight
        let mut score : Float := 0.0
        for dd in [0:headDim] do
          let qVal := (getFloat32 Q (q * headDim + dd)).toFloat
          let kVal := (getFloat32 K (k * headDim + dd)).toFloat
          score := score + qVal * kVal
        score := score * scale
        let weight := Float.exp (score - maxScore) / sumExp
        let vVal := (getFloat32 V (k * headDim + d)).toFloat
        outVal := outVal + weight * vVal
      output := setFloat32 output (q * headDim + d) outVal.toFloat32

  output

-- Compare two Float32 arrays element-wise
def compareArrays (name : String) (expected actual : ByteArray) (n : Nat) (tolerance : Float := 0.01) : IO Bool := do
  let mut maxError : Float := 0.0
  let mut totalError : Float := 0.0
  let mut errors := 0

  for i in [0:n] do
    let exp := (getFloat32 expected i).toFloat
    let act := (getFloat32 actual i).toFloat
    let err := (exp - act).abs
    let relErr := if exp.abs > 0.0001 then err / exp.abs else err
    maxError := if relErr > maxError then relErr else maxError
    totalError := totalError + relErr
    if relErr > tolerance then
      errors := errors + 1
      if errors <= 5 then
        IO.println s!"  [{i}] expected {exp}, got {act}, error {relErr * 100}%"

  let avgError := totalError / n.toFloat
  if maxError < tolerance then
    IO.println s!"  {name}: PASS (max error {maxError * 100}%, avg {avgError * 100}%)"
    return true
  else
    IO.println s!"  {name}: FAIL ({errors} errors, max {maxError * 100}%, avg {avgError * 100}%)"
    return false

def main : IO Unit := do
  IO.println "=== Flash Attention Test ==="
  IO.println ""

  -- Test 1: Small attention (4 queries, 8 dim)
  IO.println "Test 1: Small attention (seq=4, dim=8)"
  let seqLen1 := 4
  let headDim1 := 8
  let n1 := seqLen1 * headDim1

  -- Use simple values: all ones (attention should give uniform weights)
  let q1 := fillFloat32 n1 1.0
  let k1 := fillFloat32 n1 1.0
  let v1 := fillFloat32 n1 1.0

  let cpuOut1 := cpuAttention seqLen1 headDim1 q1 k1 v1
  let gpuOut1 := Metal.Float32.flashAttention seqLen1.toUSize headDim1.toUSize q1 k1 v1

  IO.println s!"  CPU output sum: {sumFloat32 cpuOut1 n1}"
  IO.println s!"  GPU output sum: {sumFloat32 gpuOut1 n1}"
  let _ ← compareArrays "Uniform weights" cpuOut1 gpuOut1 n1
  IO.println ""

  -- Test 2: Medium attention with pseudo-random values
  IO.println "Test 2: Medium attention (seq=16, dim=32)"
  let seqLen2 := 16
  let headDim2 := 32
  let n2 := seqLen2 * headDim2

  let q2 := pseudoRandomFloat32 n2 42
  let k2 := pseudoRandomFloat32 n2 123
  let v2 := pseudoRandomFloat32 n2 456

  let cpuOut2 := cpuAttention seqLen2 headDim2 q2 k2 v2
  let gpuOut2 := Metal.Float32.flashAttention seqLen2.toUSize headDim2.toUSize q2 k2 v2

  IO.println s!"  CPU output sum: {sumFloat32 cpuOut2 n2}"
  IO.println s!"  GPU output sum: {sumFloat32 gpuOut2 n2}"
  let _ ← compareArrays "Random values" cpuOut2 gpuOut2 n2
  IO.println ""

  -- Test 3: Causal attention
  IO.println "Test 3: Causal attention (seq=8, dim=16)"
  let seqLen3 := 8
  let headDim3 := 16
  let n3 := seqLen3 * headDim3

  let q3 := pseudoRandomFloat32 n3 789
  let k3 := pseudoRandomFloat32 n3 101
  let v3 := pseudoRandomFloat32 n3 202

  let cpuCausal := cpuAttentionCausal seqLen3 headDim3 q3 k3 v3
  let gpuCausal := Metal.Float32.flashAttentionCausal seqLen3.toUSize headDim3.toUSize q3 k3 v3
  IO.println s!"  CPU causal sum: {sumFloat32 cpuCausal n3}"
  IO.println s!"  GPU causal sum: {sumFloat32 gpuCausal n3}"
  let _ ← compareArrays "Causal attention" cpuCausal gpuCausal n3
  IO.println ""

  -- Test 4: Batched softmax
  IO.println "Test 4: Batched softmax (32 rows × 64 cols)"
  let numRows := 32
  let rowSize := 64
  let nSoftmax := numRows * rowSize

  let softmaxInput := pseudoRandomFloat32 nSoftmax 303
  let softmaxOut := Metal.Float32.softmaxBatched numRows.toUSize rowSize.toUSize softmaxInput

  -- Check that each row sums to 1
  let mut softmaxOk := true
  for row in [0:numRows] do
    let mut rowSum : Float := 0.0
    for col in [0:rowSize] do
      rowSum := rowSum + (getFloat32 softmaxOut (row * rowSize + col)).toFloat
    if (rowSum - 1.0).abs > 0.01 then
      IO.println s!"  Row {row} sum: {rowSum} (expected 1.0)"
      softmaxOk := false

  if softmaxOk then
    IO.println s!"  Batched softmax: PASS (all rows sum to 1.0)"
  else
    IO.println s!"  Batched softmax: FAIL (rows don't sum to 1.0)"
  IO.println ""

  IO.println "=== Done ==="
