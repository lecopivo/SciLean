/-
GPU-Accelerated MNIST Training

A 2-layer MLP trained entirely on GPU using Metal:
  Input: 784 (28×28 flattened)
  Hidden: 128 with GELU
  Output: 10 with softmax

Uses SciLean's Metal backend for all operations:
- Forward: gemm → biasGelu → gemm → softmax
- Backward: softmaxBackward → gemmTN/gemmNT → geluBackward → gemmTN/gemmNT
- Update: axpy (SGD)
-/

import SciLean.FFI.Metal
import SciLean.FFI.Float32Array

open SciLean.Metal

/-! ## ByteArray Helpers -/

/-- Read a Float32 from ByteArray at byte index -/
def readFloat32 (arr : ByteArray) (byteIdx : Nat) : Float :=
  (arr.ugetFloat32 byteIdx.toUSize).toFloat

/-- Write a Float32 to ByteArray at byte index -/
def writeFloat32 (arr : ByteArray) (byteIdx : Nat) (val : Float) : ByteArray :=
  arr.usetFloat32 byteIdx.toUSize val.toFloat32

/-! ## Data Loading (same as SimpleMNIST) -/

def checkFileExists (path : System.FilePath) : IO Unit := do
  if ¬(← path.pathExists) then
     throw (IO.userError s!"MNIST data file '{path}' not found. Please download from https://git-disl.github.io/GTDLBench/datasets/mnist_datasets/")

def loadImagesRaw (path : System.FilePath) (maxImages : Nat) : IO ByteArray := do
  checkFileExists path
  if maxImages = 0 then return ByteArray.empty

  let start ← IO.monoMsNow
  IO.print s!"Loading images from {path}... "

  let content ← IO.FS.readBinFile path
  -- Skip 16-byte header
  let data := content.extract 16 (16 + maxImages * 784)

  if data.size < maxImages * 784 then
    throw <| IO.userError s!"File {path} contains insufficient data"

  -- Convert to Float32 ByteArray (normalized to [0,1])
  let mut result := ByteArray.replicateFloat32 (maxImages * 784) 0.0
  for i in [0:maxImages * 784] do
    let byteVal := data.get! i
    let floatVal : Float32 := (byteVal.toNat.toFloat / 255.0).toFloat32
    result := result.usetFloat32 (i * 4).toUSize floatVal

  IO.println s!"done ({(← IO.monoMsNow) - start}ms)"
  return result

def loadLabelsRaw (path : System.FilePath) (maxLabels : Nat) : IO ByteArray := do
  checkFileExists path
  if maxLabels = 0 then return ByteArray.empty

  let start ← IO.monoMsNow
  IO.print s!"Loading labels from {path}... "

  let content ← IO.FS.readBinFile path
  -- Skip 8-byte header
  let data := content.extract 8 (8 + maxLabels)

  if data.size < maxLabels then
    throw <| IO.userError s!"File {path} contains insufficient labels"

  -- Convert to one-hot Float32 ByteArray
  let mut result := ByteArray.replicateFloat32 (maxLabels * 10) 0.0
  for i in [0:maxLabels] do
    let labelIdx := data.get! i
    for j in [0:10] do
      let val : Float32 := if j = labelIdx.toNat then 1.0 else 0.0
      result := result.usetFloat32 ((i * 10 + j) * 4).toUSize val

  IO.println s!"done ({(← IO.monoMsNow) - start}ms)"
  return result

/-! ## Weight Initialization -/

def initWeightsRaw (rows cols : Nat) (scale : Float) : IO ByteArray := do
  let size := rows * cols
  let mut result := ByteArray.replicateFloat32 size 0.0
  for i in [0:size] do
    let r := (← IO.rand 0 10000).toFloat / 10000.0
    let val : Float32 := (r * scale - scale / 2.0).toFloat32
    result := result.usetFloat32 (i * 4).toUSize val
  return result

def initZerosRaw (size : Nat) : ByteArray :=
  ByteArray.replicateFloat32 size 0.0

/-! ## GPU Weight Structure -/

structure GpuWeights where
  w1 : GpuBuffer  -- [128, 784]
  b1 : GpuBuffer  -- [128]
  w2 : GpuBuffer  -- [10, 128]
  b2 : GpuBuffer  -- [10]

structure GpuGradients where
  dw1 : GpuBuffer
  db1 : GpuBuffer
  dw2 : GpuBuffer
  db2 : GpuBuffer

/-! ## Forward Pass -/

/-- Forward pass: x → h = gelu(W1 @ x + b1) → o = W2 @ h + b2 → softmax(o)
    Returns (softmax_output, hidden_pre_activation, hidden_post_activation)
    for use in backward pass -/
def forwardBatch (weights : GpuWeights) (x : GpuBuffer)
    (batchSize : USize) : IO (GpuBuffer × GpuBuffer × GpuBuffer × GpuBuffer) := do
  -- x is [batchSize, 784] stored as [batchSize * 784]
  -- W1 is [128, 784], b1 is [128]
  -- h = gelu(x @ W1^T + b1)

  -- First layer: h_pre = x @ W1^T, result is [batchSize, 128]
  -- x[batch, 784] @ W1^T[784, 128] = h_pre[batch, 128]
  let h_pre ← GpuBuffer.gemmNT x weights.w1 batchSize 784 128

  -- Fused bias + gelu: h = gelu(h_pre + b1)
  let h ← GpuBuffer.biasGelu h_pre weights.b1 (batchSize * 128) 128

  -- Second layer: o_pre = h @ W2^T, result is [batchSize, 10]
  let o_pre ← GpuBuffer.gemmNT h weights.w2 batchSize 128 10

  -- Add bias to output
  let o ← GpuBuffer.add o_pre weights.b2 (batchSize * 10)

  -- Softmax
  let y ← GpuBuffer.softmax o batchSize 10

  return (y, h_pre, h, o)

/-! ## Backward Pass -/

/-- Backward pass: computes gradients for all weights
    Returns gradients for w1, b1, w2, b2 -/
def backwardBatch (weights : GpuWeights) (x y target h_pre h : GpuBuffer)
    (batchSize : USize) : IO GpuGradients := do
  -- dL/do = y - target (softmax + cross-entropy combined gradient)
  let d_o ← GpuBuffer.sub y target (batchSize * 10)

  -- dL/dW2 = h^T @ d_o, h is [batch, 128], d_o is [batch, 10]
  -- h^T[128, batch] @ d_o[batch, 10] = dW2[128, 10]
  -- But we want dW2 in [10, 128] format, so we compute d_o^T @ h
  let dw2 ← GpuBuffer.gemmTN d_o h 10 batchSize 128

  -- dL/db2 = sum(d_o, axis=0) - column-wise sum gives [10]
  let db2 ← GpuBuffer.colSum d_o batchSize 10

  -- dL/dh = d_o @ W2, d_o is [batch, 10], W2 is [10, 128]
  let d_h ← GpuBuffer.gemm d_o weights.w2 batchSize 10 128

  -- dL/dh_pre = d_h * gelu'(h_pre)
  let d_h_pre ← GpuBuffer.geluBackward h_pre d_h (batchSize * 128)

  -- dL/dW1 = x^T @ d_h_pre, x is [batch, 784], d_h_pre is [batch, 128]
  -- x^T[784, batch] @ d_h_pre[batch, 128] = dW1[784, 128]
  -- But we want dW1 in [128, 784] format, so we compute d_h_pre^T @ x
  let dw1 ← GpuBuffer.gemmTN d_h_pre x 128 batchSize 784

  -- dL/db1 = sum(d_h_pre, axis=0) - column-wise sum gives [128]
  let db1 ← GpuBuffer.colSum d_h_pre batchSize 128

  return { dw1 := dw1, db1 := db1, dw2 := dw2, db2 := db2 }

/-! ## SGD Update -/

/-- SGD update: w = w - lr * grad -/
def sgdUpdate (weights : GpuWeights) (grads : GpuGradients)
    (lr : Float) : IO GpuWeights := do
  -- w1 = w1 - lr * dw1
  let w1' ← GpuBuffer.axpy (128 * 784) (-lr) grads.dw1 weights.w1
  let b1' ← GpuBuffer.axpy 128 (-lr) grads.db1 weights.b1
  let w2' ← GpuBuffer.axpy (10 * 128) (-lr) grads.dw2 weights.w2
  let b2' ← GpuBuffer.axpy 10 (-lr) grads.db2 weights.b2

  return { w1 := w1', b1 := b1', w2 := w2', b2 := b2' }

/-! ## Loss and Accuracy -/

/-- Compute cross-entropy loss (download to CPU for now) -/
def computeLoss (pred target : GpuBuffer) (batchSize : USize) : IO Float := do
  let predData ← pred.toByteArray
  let targetData ← target.toByteArray

  let eps : Float := 1e-7
  let n := batchSize.toNat

  let mut loss : Float := 0
  for i in [0:n] do
    for j in [0:10] do
      let idx := (i * 10 + j) * 4
      let p := readFloat32 predData idx
      let t := readFloat32 targetData idx
      loss := loss - t * Float.log (p + eps)

  return loss / n.toFloat

/-- Compute accuracy (download to CPU) -/
def computeAccuracy (pred target : GpuBuffer) (batchSize : USize) : IO Float := do
  let predData ← pred.toByteArray
  let targetData ← target.toByteArray

  let n := batchSize.toNat

  let mut correct : Nat := 0
  for i in [0:n] do
    let mut predMax : Float := -1e10
    let mut targMax : Float := -1e10
    let mut predIdx : Nat := 0
    let mut targIdx : Nat := 0

    for j in [0:10] do
      let idx := (i * 10 + j) * 4
      let p := readFloat32 predData idx
      let t := readFloat32 targetData idx

      if p > predMax then
        predMax := p
        predIdx := j
      if t > targMax then
        targMax := t
        targIdx := j

    if predIdx = targIdx then
      correct := correct + 1

  return correct.toFloat / n.toFloat

/-! ## Training Loop -/

def trainEpoch (weights : GpuWeights) (images labels : GpuBuffer)
    (numSamples batchSize : Nat) (lr : Float) : IO GpuWeights := do
  let mut w := weights
  let numBatches := numSamples / batchSize

  for batch in [0:numBatches] do
    -- Get batch slice (for simplicity, we process all data as one batch for now)
    -- In a real implementation, you'd slice the buffers

    -- Forward pass
    let (pred, h_pre, h, _) ← forwardBatch w images batchSize.toUSize

    -- Backward pass
    let grads ← backwardBatch w images pred labels h_pre h batchSize.toUSize

    -- SGD update
    w ← sgdUpdate w grads lr

    if batch % 10 = 0 then
      IO.print "."

  return w

/-! ## Main -/

def main : IO Unit := do
  IO.println "GPU-Accelerated MNIST Training (Metal)"
  IO.println "========================================"

  -- Check Metal availability
  if !isAvailable () then
    throw (IO.userError "Metal GPU not available")
  IO.println "Metal GPU: available"

  -- Configuration
  let numTrain := 1000  -- Number of training samples
  let batchSize := numTrain  -- Process all as one batch for simplicity
  let epochs := 50
  -- Gradients are summed over batch (not averaged), so effective lr = lr * batchSize
  -- With batchSize=1000, lr=0.0005 gives effective step size of 0.5
  let lr := 0.0005

  -- Load training data
  let imageData ← loadImagesRaw "data/train-images-idx3-ubyte" numTrain
  let labelData ← loadLabelsRaw "data/train-labels-idx1-ubyte" numTrain

  IO.println s!"Loaded {numTrain} training samples"

  -- Initialize weights (He initialization)
  let scale1 := Float.sqrt (2.0 / 784.0)
  let scale2 := Float.sqrt (2.0 / 128.0)

  IO.print "Initializing weights... "
  let w1Data ← initWeightsRaw 128 784 scale1
  let b1Data := initZerosRaw 128
  let w2Data ← initWeightsRaw 10 128 scale2
  let b2Data := initZerosRaw 10
  IO.println "done"

  -- Upload to GPU
  IO.print "Uploading to GPU... "
  let images ← GpuBuffer.fromByteArray imageData
  let labels ← GpuBuffer.fromByteArray labelData
  let w1 ← GpuBuffer.fromByteArray w1Data
  let b1 ← GpuBuffer.fromByteArray b1Data
  let w2 ← GpuBuffer.fromByteArray w2Data
  let b2 ← GpuBuffer.fromByteArray b2Data
  IO.println "done"

  let initialWeights : GpuWeights := { w1 := w1, b1 := b1, w2 := w2, b2 := b2 }

  -- Initial accuracy
  let (initPred, _, _, _) ← forwardBatch initialWeights images batchSize.toUSize
  let initAcc ← computeAccuracy initPred labels batchSize.toUSize
  IO.println s!"Initial accuracy: {initAcc * 100}%"

  -- Training loop
  IO.println "\nTraining..."
  let mut weights := initialWeights

  for epoch in [0:epochs] do
    let start ← IO.monoMsNow

    -- Forward pass
    let (pred, h_pre, h, _) ← forwardBatch weights images batchSize.toUSize

    -- Backward pass
    let grads ← backwardBatch weights images pred labels h_pre h batchSize.toUSize

    -- SGD update
    weights ← sgdUpdate weights grads lr

    let elapsed := (← IO.monoMsNow) - start

    -- Compute accuracy
    let (pred2, _, _, _) ← forwardBatch weights images batchSize.toUSize
    let acc ← computeAccuracy pred2 labels batchSize.toUSize

    IO.println s!"Epoch {epoch + 1}: accuracy = {acc * 100}%, time = {elapsed}ms"

  -- Final results
  let (finalPred, _, _, _) ← forwardBatch weights images batchSize.toUSize
  let finalAcc ← computeAccuracy finalPred labels batchSize.toUSize
  IO.println s!"\nFinal accuracy: {finalAcc * 100}%"

  IO.println "\nDone!"
