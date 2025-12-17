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

Type Safety: Uses CpuBuffer/GpuBuffer to enforce explicit data transfers.
All GPU<->CPU transfers must use `.upload` or `.download` - no implicit coercions!
-/

import SciLean.FFI.Metal
import SciLean.FFI.Float32Array

open SciLean.Metal

/-! ## CpuBuffer Helpers -/

namespace SciLean.Metal.CpuBuffer

/-- Read a Float32 from CpuBuffer at element index -/
def readFloat32 (buf : CpuBuffer) (elemIdx : Nat) : Float :=
  (buf.data.ugetFloat32 (elemIdx * 4).toUSize).toFloat

/-- Write a Float32 to CpuBuffer at element index -/
def writeFloat32 (buf : CpuBuffer) (elemIdx : Nat) (val : Float) : CpuBuffer :=
  ⟨buf.data.usetFloat32 (elemIdx * 4).toUSize val.toFloat32⟩

end SciLean.Metal.CpuBuffer

/-! ## Data Loading (returns CpuBuffer for type safety) -/

def checkFileExists (path : System.FilePath) : IO Unit := do
  if ¬(← path.pathExists) then
     throw (IO.userError s!"MNIST data file '{path}' not found. Please download from https://git-disl.github.io/GTDLBench/datasets/mnist_datasets/")

/-- Load MNIST images to CPU buffer (explicit CPU-resident data) -/
def loadImagesCpu (path : System.FilePath) (maxImages : Nat) : IO CpuBuffer := do
  checkFileExists path
  if maxImages = 0 then return CpuBuffer.zeros 0

  let start ← IO.monoMsNow
  IO.print s!"Loading images from {path}... "

  let content ← IO.FS.readBinFile path
  -- Skip 16-byte header
  let data := content.extract 16 (16 + maxImages * 784)

  if data.size < maxImages * 784 then
    throw <| IO.userError s!"File {path} contains insufficient data"

  -- Convert to Float32 CpuBuffer (normalized to [0,1])
  let mut result := ByteArray.replicateFloat32 (maxImages * 784) 0.0
  for i in [0:maxImages * 784] do
    let byteVal := data.get! i
    let floatVal : Float32 := (byteVal.toNat.toFloat / 255.0).toFloat32
    result := result.usetFloat32 (i * 4).toUSize floatVal

  IO.println s!"done ({(← IO.monoMsNow) - start}ms)"
  return CpuBuffer.mk result

/-- Load MNIST labels to CPU buffer (explicit CPU-resident data) -/
def loadLabelsCpu (path : System.FilePath) (maxLabels : Nat) : IO CpuBuffer := do
  checkFileExists path
  if maxLabels = 0 then return CpuBuffer.zeros 0

  let start ← IO.monoMsNow
  IO.print s!"Loading labels from {path}... "

  let content ← IO.FS.readBinFile path
  -- Skip 8-byte header
  let data := content.extract 8 (8 + maxLabels)

  if data.size < maxLabels then
    throw <| IO.userError s!"File {path} contains insufficient labels"

  -- Convert to one-hot Float32 CpuBuffer
  let mut result := ByteArray.replicateFloat32 (maxLabels * 10) 0.0
  for i in [0:maxLabels] do
    let labelIdx := data.get! i
    for j in [0:10] do
      let val : Float32 := if j = labelIdx.toNat then 1.0 else 0.0
      result := result.usetFloat32 ((i * 10 + j) * 4).toUSize val

  IO.println s!"done ({(← IO.monoMsNow) - start}ms)"
  return CpuBuffer.mk result

/-! ## Weight Initialization (returns CpuBuffer) -/

/-- Initialize weights on CPU with random values -/
def initWeightsCpu (rows cols : Nat) (scale : Float) : IO CpuBuffer := do
  let size := rows * cols
  let mut result := ByteArray.replicateFloat32 size 0.0
  for i in [0:size] do
    let r := (← IO.rand 0 10000).toFloat / 10000.0
    let val : Float32 := (r * scale - scale / 2.0).toFloat32
    result := result.usetFloat32 (i * 4).toUSize val
  return CpuBuffer.mk result

/-- Initialize zero buffer on CPU -/
def initZerosCpu (size : Nat) : CpuBuffer :=
  CpuBuffer.zeros size

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

/-- Forward pass (internal, no batching): x → h = gelu(W1 @ x + b1) → o = W2 @ h + b2 → softmax(o)
    Returns (softmax_output, hidden_pre_activation, hidden_post_activation)
    for use in backward pass -/
def forwardBatchInternal (weights : GpuWeights) (x : GpuBuffer)
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
  let o ← GpuBuffer.biasAdd o_pre weights.b2 (batchSize * 10) 10

  -- Softmax
  let y ← GpuBuffer.softmax o batchSize 10

  return (y, h_pre, h, o)

/-- Forward pass with command buffer batching -/
def forwardBatch (weights : GpuWeights) (x : GpuBuffer)
    (batchSize : USize) : IO (GpuBuffer × GpuBuffer × GpuBuffer × GpuBuffer) :=
  withBatch (forwardBatchInternal weights x batchSize)

/-! ## Backward Pass -/

/-- Backward pass (internal, no batching): computes gradients for all weights
    Returns gradients for w1, b1, w2, b2 -/
def backwardBatchInternal (weights : GpuWeights) (x y target h_pre h : GpuBuffer)
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

/-- Backward pass with command buffer batching -/
def backwardBatch (weights : GpuWeights) (x y target h_pre h : GpuBuffer)
    (batchSize : USize) : IO GpuGradients :=
  withBatch (backwardBatchInternal weights x y target h_pre h batchSize)

/-! ## SGD Update -/

/-- SGD update (internal, no batching): w = w - lr * grad -/
def sgdUpdateInternal (weights : GpuWeights) (grads : GpuGradients)
    (lr : Float) : IO GpuWeights := do
  -- w1 = w1 - lr * dw1
  let w1' ← GpuBuffer.axpy (128 * 784) (-lr) grads.dw1 weights.w1
  let b1' ← GpuBuffer.axpy 128 (-lr) grads.db1 weights.b1
  let w2' ← GpuBuffer.axpy (10 * 128) (-lr) grads.dw2 weights.w2
  let b2' ← GpuBuffer.axpy 10 (-lr) grads.db2 weights.b2

  return { w1 := w1', b1 := b1', w2 := w2', b2 := b2' }

/-- SGD update with command buffer batching -/
def sgdUpdate (weights : GpuWeights) (grads : GpuGradients)
    (lr : Float) : IO GpuWeights :=
  withBatch (sgdUpdateInternal weights grads lr)

/-! ## Debug Helpers -/

/-- Print buffer statistics for debugging (explicitly downloads from GPU) -/
def debugBuffer (name : String) (gpuBuf : GpuBuffer) (n : Nat) : IO Unit := do
  -- EXPLICIT download from GPU to CPU
  let cpuBuf ← gpuBuf.download
  let mut sum : Float := 0
  let mut minVal : Float := Float.inf
  let mut maxVal : Float := Float.negInf
  let mut hasNaN := false
  let mut hasInf := false
  let mut numZeros : Nat := 0
  for i in [0:n] do
    let val := cpuBuf.readFloat32 i
    if val.isNaN then hasNaN := true
    if val.isInf then hasInf := true
    if val == 0.0 then numZeros := numZeros + 1
    sum := sum + val
    if val < minVal then minVal := val
    if val > maxVal then maxVal := val
  let mean := sum / n.toFloat
  IO.println s!"  {name}: mean={mean}, min={minVal}, max={maxVal}, zeros={numZeros}/{n}, hasNaN={hasNaN}, hasInf={hasInf}"

/-- Diagnostic forward pass that prints intermediate values -/
def forwardBatchDiag (weights : GpuWeights) (x : GpuBuffer)
    (batchSize : USize) : IO (GpuBuffer × GpuBuffer × GpuBuffer × GpuBuffer) := do
  IO.println s!"  --- Forward pass diagnostics (batch={batchSize}) ---"

  debugBuffer "input x" x (batchSize.toNat * 784)

  -- First layer: h_pre = x @ W1^T
  let h_pre ← GpuBuffer.gemmNT x weights.w1 batchSize 784 128
  debugBuffer "h_pre (after gemmNT)" h_pre (batchSize.toNat * 128)

  -- Fused bias + gelu
  let h ← GpuBuffer.biasGelu h_pre weights.b1 (batchSize * 128) 128
  debugBuffer "h (after biasGelu)" h (batchSize.toNat * 128)

  -- Second layer: o_pre = h @ W2^T
  let o_pre ← GpuBuffer.gemmNT h weights.w2 batchSize 128 10
  debugBuffer "o_pre (after gemmNT)" o_pre (batchSize.toNat * 10)

  -- Add bias
  let o ← GpuBuffer.biasAdd o_pre weights.b2 (batchSize * 10) 10
  debugBuffer "o (before softmax)" o (batchSize.toNat * 10)

  -- Softmax
  let y ← GpuBuffer.softmax o batchSize 10
  debugBuffer "y (softmax out)" y (batchSize.toNat * 10)

  return (y, h_pre, h, o)

/-- Diagnostic backward pass that prints intermediate values -/
def backwardBatchDiag (weights : GpuWeights) (x y target h_pre h : GpuBuffer)
    (batchSize : USize) : IO GpuGradients := do
  IO.println s!"  --- Backward pass diagnostics (batch={batchSize}) ---"

  -- dL/do = y - target (softmax + cross-entropy combined gradient)
  let d_o ← GpuBuffer.sub y target (batchSize * 10)
  debugBuffer "d_o (y-target)" d_o (batchSize.toNat * 10)

  -- dL/dW2 = h^T @ d_o
  let dw2 ← GpuBuffer.gemmTN d_o h 10 batchSize 128
  debugBuffer "dw2" dw2 (10 * 128)

  -- dL/db2 = sum(d_o, axis=0)
  let db2 ← GpuBuffer.colSum d_o batchSize 10
  debugBuffer "db2" db2 10

  -- dL/dh = d_o @ W2
  let d_h ← GpuBuffer.gemm d_o weights.w2 batchSize 10 128
  debugBuffer "d_h" d_h (batchSize.toNat * 128)

  -- dL/dh_pre = d_h * gelu'(h_pre)
  let d_h_pre ← GpuBuffer.geluBackward h_pre d_h (batchSize * 128)
  debugBuffer "d_h_pre" d_h_pre (batchSize.toNat * 128)

  -- dL/dW1 = x^T @ d_h_pre
  let dw1 ← GpuBuffer.gemmTN d_h_pre x 128 batchSize 784
  debugBuffer "dw1" dw1 (128 * 784)

  -- dL/db1 = sum(d_h_pre, axis=0)
  let db1 ← GpuBuffer.colSum d_h_pre batchSize 128
  debugBuffer "db1" db1 128

  return { dw1 := dw1, db1 := db1, dw2 := dw2, db2 := db2 }

/-! ## Loss and Accuracy -/

/-- Compute cross-entropy loss (EXPLICIT download to CPU) -/
def computeLoss (gpuPred gpuTarget : GpuBuffer) (batchSize : USize) : IO Float := do
  -- EXPLICIT download from GPU to CPU
  let pred ← gpuPred.download
  let target ← gpuTarget.download

  let eps : Float := 1e-7
  let n := batchSize.toNat

  let mut loss : Float := 0
  for i in [0:n] do
    for j in [0:10] do
      let idx := i * 10 + j
      let p := pred.readFloat32 idx
      let t := target.readFloat32 idx
      loss := loss - t * Float.log (p + eps)

  return loss / n.toFloat

/-- Compute accuracy (EXPLICIT download to CPU) -/
def computeAccuracy (gpuPred gpuTarget : GpuBuffer) (batchSize : USize) : IO Float := do
  -- EXPLICIT download from GPU to CPU
  let pred ← gpuPred.download
  let target ← gpuTarget.download

  let n := batchSize.toNat

  let mut correct : Nat := 0
  for i in [0:n] do
    let mut predMax : Float := -1e10
    let mut targMax : Float := -1e10
    let mut predIdx : Nat := 0
    let mut targIdx : Nat := 0

    for j in [0:10] do
      let idx := i * 10 + j
      let p := pred.readFloat32 idx
      let t := target.readFloat32 idx

      if p > predMax then
        predMax := p
        predIdx := j
      if t > targMax then
        targMax := t
        targIdx := j

    if predIdx = targIdx then
      correct := correct + 1

  return correct.toFloat / n.toFloat

/-! ## Diagnostic Functions -/

/-- Run diagnostic test comparing different batch sizes -/
def diagBatchSizes (cpuImages cpuLabels : CpuBuffer)
    (cpuW1 cpuB1 cpuW2 cpuB2 : CpuBuffer) : IO Unit := do
  IO.println "\n=== Batch Size Diagnostic Test ==="

  for testBatch in [1000, 2000, 3000, 4000] do
    IO.println s!"\n--- Testing batch size {testBatch} ---"

    -- EXPLICIT upload from CPU to GPU
    let images ← cpuImages.upload
    let labels ← cpuLabels.upload
    let w1 ← cpuW1.upload
    let b1 ← cpuB1.upload
    let w2 ← cpuW2.upload
    let b2 ← cpuB2.upload
    let weights : GpuWeights := { w1, b1, w2, b2 }

    -- Forward pass with diagnostics
    let (pred, h_pre, h, _) ← forwardBatchDiag weights images testBatch.toUSize

    -- Diagnostic backward pass
    let grads ← backwardBatchDiag weights images pred labels h_pre h testBatch.toUSize

    -- Check weight update
    let lr := 0.0005
    let weights' ← sgdUpdate weights grads lr
    debugBuffer "w1 after update" weights'.w1 (128 * 784)

    -- Check accuracy before and after
    let (pred2, _, _, _) ← forwardBatch weights' images testBatch.toUSize
    let acc ← computeAccuracy pred2 labels testBatch.toUSize
    IO.println s!"  Accuracy after 1 step: {acc * 100}%"

/-! ## Training Loop -/

/-- Combined training step: forward + backward + update in a single command buffer.
    This eliminates per-operation dispatch overhead for maximum throughput.
    lr should already be scaled for batch size (lr_effective = lr / batchSize for averaging). -/
def trainStep (weights : GpuWeights) (images labels : GpuBuffer)
    (batchSize : USize) (lr : Float) : IO GpuWeights :=
  withBatch do
    -- Forward pass
    let (pred, h_pre, h, _) ← forwardBatchInternal weights images batchSize

    -- Backward pass
    let grads ← backwardBatchInternal weights images pred labels h_pre h batchSize

    -- SGD update
    sgdUpdateInternal weights grads lr

/-- Train one epoch with mini-batching: iterates through all samples in mini-batches.
    Uses GPU buffer slicing to extract each mini-batch. -/
def trainEpochMiniBatch (weights : GpuWeights) (images labels : GpuBuffer)
    (numSamples miniBatchSize : Nat) (lr : Float) : IO GpuWeights := do
  let mut w := weights
  let numBatches := numSamples / miniBatchSize

  for batchIdx in [0:numBatches] do
    -- Calculate slice offsets (in float32 elements)
    let imageOffset := batchIdx * miniBatchSize * 784
    let labelOffset := batchIdx * miniBatchSize * 10

    -- Slice out this mini-batch (GPU-to-GPU copy)
    let batchImages ← GpuBuffer.slice images imageOffset.toUSize (miniBatchSize * 784).toUSize
    let batchLabels ← GpuBuffer.slice labels labelOffset.toUSize (miniBatchSize * 10).toUSize

    -- Training step on this mini-batch
    w ← trainStep w batchImages batchLabels miniBatchSize.toUSize lr

  return w

/-! ## Main -/

def main : IO Unit := do
  IO.println "GPU-Accelerated MNIST Training (Metal)"
  IO.println "========================================"
  IO.println "Using type-safe CpuBuffer/GpuBuffer API (no implicit coercions!)"

  -- Check Metal availability
  if !isAvailable () then
    throw (IO.userError "Metal GPU not available")
  IO.println "Metal GPU: available"

  -- Configuration
  let numTrain := 60000  -- Full MNIST training set
  let miniBatchSize := 256  -- Mini-batch size for training
  let evalBatchSize := 1000  -- Batch size for evaluation
  let epochs := 10
  -- Learning rate: gradients are summed over mini-batch, so we scale lr inversely
  -- lr_effective = baseLr / miniBatchSize gives averaged gradients
  let baseLr := 0.5
  let lr := baseLr / miniBatchSize.toFloat

  -- Load training data to CPU (explicit CPU-resident data)
  let cpuImages ← loadImagesCpu "data/train-images-idx3-ubyte" numTrain
  let cpuLabels ← loadLabelsCpu "data/train-labels-idx1-ubyte" numTrain

  IO.println s!"Loaded {numTrain} training samples to CPU"

  -- Initialize weights on CPU (He initialization)
  let scale1 := Float.sqrt (2.0 / 784.0)
  let scale2 := Float.sqrt (2.0 / 128.0)

  IO.print "Initializing weights on CPU... "
  let cpuW1 ← initWeightsCpu 128 784 scale1
  let cpuB1 := initZerosCpu 128
  let cpuW2 ← initWeightsCpu 10 128 scale2
  let cpuB2 := initZerosCpu 10
  IO.println "done"

  -- EXPLICIT upload to GPU (type system enforces this!)
  IO.print "Uploading to GPU (explicit transfer)... "
  let images ← cpuImages.upload
  let labels ← cpuLabels.upload
  let w1 ← cpuW1.upload
  let b1 ← cpuB1.upload
  let w2 ← cpuW2.upload
  let b2 ← cpuB2.upload
  IO.println "done"

  let initialWeights : GpuWeights := { w1 := w1, b1 := b1, w2 := w2, b2 := b2 }

  -- For evaluation, use first evalBatchSize samples
  let evalImages ← GpuBuffer.slice images 0 (evalBatchSize * 784).toUSize
  let evalLabels ← GpuBuffer.slice labels 0 (evalBatchSize * 10).toUSize

  -- Initial accuracy (downloads from GPU internally)
  let (initPred, _, _, _) ← forwardBatch initialWeights evalImages evalBatchSize.toUSize
  let initAcc ← computeAccuracy initPred evalLabels evalBatchSize.toUSize
  IO.println s!"Initial accuracy: {initAcc * 100}%"

  -- Training loop with mini-batching
  IO.println s!"\nTraining ({numTrain} samples, mini-batch={miniBatchSize})..."
  let mut weights := initialWeights

  for epoch in [0:epochs] do
    let start ← IO.monoMsNow

    -- Train one epoch: iterate through all mini-batches
    weights ← trainEpochMiniBatch weights images labels numTrain miniBatchSize lr

    let elapsed := (← IO.monoMsNow) - start

    -- Compute accuracy on evaluation set
    let (pred, _, _, _) ← forwardBatch weights evalImages evalBatchSize.toUSize
    let acc ← computeAccuracy pred evalLabels evalBatchSize.toUSize

    let numBatches := numTrain / miniBatchSize
    IO.println s!"Epoch {epoch + 1}: accuracy = {acc * 100}%, time = {elapsed}ms ({numBatches} batches)"

  -- Final results
  let (finalPred, _, _, _) ← forwardBatch weights evalImages evalBatchSize.toUSize
  let finalAcc ← computeAccuracy finalPred evalLabels evalBatchSize.toUSize
  IO.println s!"\nFinal accuracy: {finalAcc * 100}%"

  IO.println "\nDone!"
