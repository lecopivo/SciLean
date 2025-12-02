/-
Verify PyTorch MNIST model: Load exported weights, run inference, compare to Python.

This tests the full pipeline:
1. Load .npy weights exported from PyTorch
2. Run forward pass in Lean
3. Compare outputs to Python's expected results
-/
import SciLean
import SciLean.Data.Npy
import SciLean.Data.DataArray.TensorOperations

open SciLean

/-! ## Simple MLP Forward Pass

Architecture: 784 → 128 (ReLU) → 10
-/

/-- ReLU activation for DataArrayN -/
def relu {ι : Type} {n : Nat} [IndexType ι n] [Fold ι] (x : Float^[ι]) : Float^[ι] :=
  x.mapMono (fun v => if v > 0 then v else 0)

/-- Single MLP forward pass using DataArrayN: y = W2 @ relu(W1 @ x + b1) + b2 -/
def mlpForward
    (w1 : Float^[128, 784]) (b1 : Float^[128])
    (w2 : Float^[10, 128]) (b2 : Float^[10])
    (x : Float^[784]) : Float^[10] :=
  -- h = W1 @ x + b1
  let h : Float^[128] := DataArrayN.contractRightAddR 1.0 w1 x 0.0 0
  let h := h + b1
  -- h_relu = relu(h)
  let hRelu := relu h
  -- logits = W2 @ h_relu + b2
  let logits : Float^[10] := DataArrayN.contractRightAddR 1.0 w2 hRelu 0.0 0
  logits + b2

/-- Get argmax prediction from FloatArray -/
def argmaxArr (x : FloatArray) : Nat := Id.run do
  if x.size == 0 then return 0
  let mut maxIdx := 0
  let mut maxVal := x.uget 0 sorry_proof
  for i in [1:x.size] do
    let v := x.uget i.toUSize sorry_proof
    if v > maxVal then
      maxIdx := i
      maxVal := v
  maxIdx

/-- Check if two FloatArrays are approximately equal -/
def almostEqArr (x y : FloatArray) (tol : Float := 1e-5) : Bool := Id.run do
  if x.size != y.size then return false
  for i in [0:x.size] do
    let xi := x.uget i.toUSize sorry_proof
    let yi := y.uget i.toUSize sorry_proof
    if (xi - yi).abs > tol then
      return false
  true

def main : IO Unit := do
  IO.println "=== Verifying PyTorch MNIST Model in Lean ==="
  IO.println ""

  -- Load weights
  IO.println "Loading weights..."
  let w1 : Float^[128, 784] ← Npy.loadFloat64 "data/mnist_weights/w1.npy"
  let b1 : Float^[128] ← Npy.loadFloat64 "data/mnist_weights/b1.npy"
  let w2 : Float^[10, 128] ← Npy.loadFloat64 "data/mnist_weights/w2.npy"
  let b2 : Float^[10] ← Npy.loadFloat64 "data/mnist_weights/b2.npy"
  IO.println s!"  w1: 128x784, b1: 128, w2: 10x128, b2: 10"

  -- Load test data
  IO.println ""
  IO.println "Loading test data..."
  let testImages ← Npy.loadFile "data/mnist_weights/test_images.npy"
  let testLogits ← Npy.loadFile "data/mnist_weights/test_logits.npy"
  let testPreds ← Npy.loadFile "data/mnist_weights/test_preds.npy"
  let testLabels ← Npy.loadFile "data/mnist_weights/test_labels.npy"

  let imageFloats ← IO.ofExcept testImages.toFloatArray
  let logitFloats ← IO.ofExcept testLogits.toFloatArray
  let numTests := 10

  IO.println s!"  test_images: 10x784"
  IO.println s!"  test_logits: 10x10"

  -- Run inference and compare
  IO.println ""
  IO.println "Running inference and comparing..."

  let mut correct := 0
  let mut allMatch := true

  for testIdx in [0:numTests] do
    -- Extract single image
    let mut imgData : FloatArray := .emptyWithCapacity 784
    for j in [0:784] do
      imgData := imgData.push (imageFloats.uget (testIdx * 784 + j).toUSize sorry_proof)
    let img : Float^[784] := DataArrayN.fromFloatArray imgData

    -- Run forward pass
    let leanLogits := mlpForward w1 b1 w2 b2 img
    let leanLogitsArr := DataArrayN.toFloatArray leanLogits
    let leanPred := argmaxArr leanLogitsArr

    -- Get Python's expected logits for this sample
    let mut pyLogitsArr : FloatArray := .emptyWithCapacity 10
    for j in [0:10] do
      pyLogitsArr := pyLogitsArr.push (logitFloats.uget (testIdx * 10 + j).toUSize sorry_proof)

    -- Get Python's prediction (from test_preds as int64)
    let pyPredBytes := testPreds.data.copySlice (testPreds.startIndex + testIdx * 8) ByteArray.empty 0 8
    let pyPred := pyPredBytes[0]!.toNat  -- Simple extraction for small values

    -- Get true label (from test_labels as int64)
    let labelBytes := testLabels.data.copySlice (testLabels.startIndex + testIdx * 8) ByteArray.empty 0 8
    let trueLabel := labelBytes[0]!.toNat

    -- Check if logits match
    let logitsMatch := almostEqArr leanLogitsArr pyLogitsArr 1e-4

    -- Check predictions
    let predsMatch := leanPred == pyPred
    if leanPred == trueLabel then correct := correct + 1

    if not logitsMatch || not predsMatch then
      allMatch := false
      IO.println s!"  Sample {testIdx}: MISMATCH"
      IO.println s!"    Lean pred: {leanPred}, Python pred: {pyPred}, label: {trueLabel}"
      -- Show first few logit values for debugging
      IO.println s!"    Lean logits[0..2]: {leanLogitsArr.uget 0 sorry_proof}, {leanLogitsArr.uget 1 sorry_proof}, {leanLogitsArr.uget 2 sorry_proof}"
      IO.println s!"    Py   logits[0..2]: {pyLogitsArr.uget 0 sorry_proof}, {pyLogitsArr.uget 1 sorry_proof}, {pyLogitsArr.uget 2 sorry_proof}"
    else
      let sym := if leanPred == trueLabel then "✓" else "✗"
      IO.println s!"  Sample {testIdx}: pred={leanPred} label={trueLabel} {sym} (logits match)"

  IO.println ""
  IO.println s!"Accuracy: {correct}/{numTests} = {100.0 * correct.toFloat / numTests.toFloat}%"

  if allMatch then
    IO.println ""
    IO.println "=== SUCCESS: All logits match Python! ==="
  else
    IO.println ""
    IO.println "=== WARNING: Some outputs did not match ==="
