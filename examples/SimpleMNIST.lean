/-
Simple Feedforward Neural Network for MNIST

A minimal 2-layer MLP classifier:
  Input: 784 (28×28 flattened)
  Hidden: 128 with GELU
  Output: 10 with softmax

Standalone version - no SciLean dependencies to avoid sorry_proof panics.
-/

/-! ## Data Loading -/

def checkFileExists (path : System.FilePath) : IO Unit := do
  if ¬(← path.pathExists) then
     throw (IO.userError s!"MNIST data file '{path}' not found. Please download from https://git-disl.github.io/GTDLBench/datasets/mnist_datasets/")

def loadImages (path : System.FilePath) (maxImages : Nat) : IO (Array (Array Float)) := do
  checkFileExists path
  if maxImages = 0 then return #[]

  let start ← IO.monoMsNow
  IO.print s!"Loading images from {path}... "

  let data ← IO.FS.withFile path .read fun m => do
    let _header ← m.read 16
    let mut data : Array ByteArray := #[]
    for _ in [0:maxImages] do
      let nums ← m.read 784
      if nums.size = 0 then break
      data := data.push nums
    pure data

  if data.size ≠ maxImages then
    throw <| IO.userError s!"File {path} contains only {data.size} images"

  -- Convert to Float arrays (flattened 28×28 → 784)
  let mut images : Array (Array Float) := #[]
  for bytes in data do
    let mut img : Array Float := Array.mkEmpty 784
    for i in [0:784] do
      let byteVal := bytes.get! i
      img := img.push (byteVal.toNat.toFloat / 255.0)
    images := images.push img

  IO.println s!"done ({(← IO.monoMsNow) - start}ms)"
  return images

def loadLabels (path : System.FilePath) (maxLabels : Nat) : IO (Array (Array Float)) := do
  checkFileExists path
  if maxLabels = 0 then return #[]

  let start ← IO.monoMsNow
  IO.print s!"Loading labels from {path}... "

  let data ← IO.FS.withFile path .read fun m => do
    let _header ← m.read 8
    m.read maxLabels.toUSize

  if data.size ≠ maxLabels then
    throw <| IO.userError s!"File {path} contains only {data.size} labels"

  -- Convert to one-hot encoding
  let mut labels : Array (Array Float) := #[]
  for b in data do
    let labelIdx := b.toNat
    let mut label : Array Float := Array.mkEmpty 10
    for i in [0:10] do
      if i = labelIdx then
        label := label.push 1.0
      else
        label := label.push 0.0
    labels := labels.push label

  IO.println s!"done ({(← IO.monoMsNow) - start}ms)"
  return labels

/-! ## Activation Functions -/

def relu (x : Float) : Float := max 0 x

def gelu (x : Float) : Float :=
  let pi : Float := 3.141592653589793
  let c := Float.sqrt (2.0 / pi)
  x * (1 + Float.tanh (c * x * (1 + 0.044715 * x^2)))

def softmax (x : Array Float) : Array Float := Id.run do
  let n := x.size
  if n = 0 then return x

  -- Find max for numerical stability
  let mut maxVal : Float := x[0]!
  for i in [1:n] do
    if x[i]! > maxVal then
      maxVal := x[i]!

  -- Compute exp(x - max) and sum
  let mut exps : Array Float := Array.mkEmpty n
  let mut sumExps : Float := 0
  for i in [0:n] do
    let e := Float.exp (x[i]! - maxVal)
    exps := exps.push e
    sumExps := sumExps + e

  -- Normalize
  let mut result : Array Float := Array.mkEmpty n
  for i in [0:n] do
    result := result.push (exps[i]! / sumExps)
  return result

/-! ## Network Definition -/

-- Weight storage using Array Float
-- w1: 128 × 784 (row-major), b1: 128, w2: 10 × 128, b2: 10
structure MLPWeights where
  w1 : Array Float  -- 128 × 784 = 100352 elements
  b1 : Array Float  -- 128 elements
  w2 : Array Float  -- 10 × 128 = 1280 elements
  b2 : Array Float  -- 10 elements

-- Forward pass: input → hidden (GELU) → output (softmax)
def forward (weights : MLPWeights) (x : Array Float) : Array Float := Id.run do
  -- Hidden layer: h = gelu(W1 * x + b1)
  let mut h : Array Float := Array.mkEmpty 128
  for i in [0:128] do
    let mut sum : Float := weights.b1[i]!
    for j in [0:784] do
      sum := sum + weights.w1[i * 784 + j]! * x[j]!
    h := h.push (gelu sum)

  -- Output layer: o = W2 * h + b2
  let mut o : Array Float := Array.mkEmpty 10
  for i in [0:10] do
    let mut sum : Float := weights.b2[i]!
    for j in [0:128] do
      sum := sum + weights.w2[i * 128 + j]! * h[j]!
    o := o.push sum

  return softmax o

-- Cross-entropy loss
def crossEntropyLoss (pred actual : Array Float) : Float := Id.run do
  let eps : Float := 1e-7
  let mut loss : Float := 0
  for i in [0:10] do
    loss := loss - actual[i]! * Float.log (pred[i]! + eps)
  return loss

-- Compute loss for a single sample
def sampleLoss (weights : MLPWeights) (x y : Array Float) : Float :=
  crossEntropyLoss (forward weights x) y

/-! ## Gradient Computation (Analytical Backpropagation) -/

-- Manual backpropagation (more efficient than numerical gradients)
def backprop (weights : MLPWeights) (x y : Array Float) : MLPWeights := Id.run do
  -- Forward pass with intermediate values stored
  let mut h_pre : Array Float := Array.mkEmpty 128  -- pre-activation hidden
  let mut h : Array Float := Array.mkEmpty 128       -- post-activation hidden

  for i in [0:128] do
    let mut sum : Float := weights.b1[i]!
    for j in [0:784] do
      sum := sum + weights.w1[i * 784 + j]! * x[j]!
    h_pre := h_pre.push sum
    h := h.push (gelu sum)

  let mut o_pre : Array Float := Array.mkEmpty 10
  for i in [0:10] do
    let mut sum : Float := weights.b2[i]!
    for j in [0:128] do
      sum := sum + weights.w2[i * 128 + j]! * h[j]!
    o_pre := o_pre.push sum

  let pred := softmax o_pre

  -- Backward pass
  -- dL/do = pred - actual (for softmax + cross-entropy)
  let mut d_o : Array Float := Array.mkEmpty 10
  for i in [0:10] do
    d_o := d_o.push (pred[i]! - y[i]!)

  -- Gradients for w2 and b2
  let mut dw2 : Array Float := Array.mkEmpty 1280
  let mut db2 : Array Float := Array.mkEmpty 10
  for i in [0:10] do
    db2 := db2.push d_o[i]!
    for j in [0:128] do
      dw2 := dw2.push (d_o[i]! * h[j]!)

  -- Backprop through hidden layer: d_h = W2^T * d_o
  let mut d_h : Array Float := Array.mkEmpty 128
  for j in [0:128] do
    let mut sum : Float := 0
    for i in [0:10] do
      sum := sum + weights.w2[i * 128 + j]! * d_o[i]!
    d_h := d_h.push sum

  -- Backprop through GELU activation
  -- Use numerical approximation for derivative
  let mut d_h_pre : Array Float := Array.mkEmpty 128
  let eps := 1e-4
  for i in [0:128] do
    let x_i := h_pre[i]!
    let gelu_deriv := (gelu (x_i + eps) - gelu (x_i - eps)) / (2 * eps)
    d_h_pre := d_h_pre.push (d_h[i]! * gelu_deriv)

  -- Gradients for w1 and b1
  let mut dw1 : Array Float := Array.mkEmpty 100352
  let mut db1 : Array Float := Array.mkEmpty 128
  for i in [0:128] do
    db1 := db1.push d_h_pre[i]!
    for j in [0:784] do
      dw1 := dw1.push (d_h_pre[i]! * x[j]!)

  { w1 := dw1, b1 := db1, w2 := dw2, b2 := db2 }

/-! ## Training -/

-- SGD update step
def sgdUpdate (weights grad : MLPWeights) (lr : Float) : MLPWeights := Id.run do
  let mut w1' : Array Float := Array.mkEmpty 100352
  for i in [0:100352] do
    w1' := w1'.push (weights.w1[i]! - lr * grad.w1[i]!)

  let mut b1' : Array Float := Array.mkEmpty 128
  for i in [0:128] do
    b1' := b1'.push (weights.b1[i]! - lr * grad.b1[i]!)

  let mut w2' : Array Float := Array.mkEmpty 1280
  for i in [0:1280] do
    w2' := w2'.push (weights.w2[i]! - lr * grad.w2[i]!)

  let mut b2' : Array Float := Array.mkEmpty 10
  for i in [0:10] do
    b2' := b2'.push (weights.b2[i]! - lr * grad.b2[i]!)

  { w1 := w1', b1 := b1', w2 := w2', b2 := b2' }

-- Initialize weights with small random values
def initWeights : IO MLPWeights := do
  let scale1 := Float.sqrt (2.0 / 784.0)  -- He initialization
  let scale2 := Float.sqrt (2.0 / 128.0)

  let mut w1 : Array Float := Array.mkEmpty 100352
  for _ in [0:100352] do
    let r := (← IO.rand 0 10000).toFloat / 10000.0
    w1 := w1.push (r * scale1 - scale1/2)

  let mut b1 : Array Float := Array.mkEmpty 128
  for _ in [0:128] do
    b1 := b1.push 0.0

  let mut w2 : Array Float := Array.mkEmpty 1280
  for _ in [0:1280] do
    let r := (← IO.rand 0 10000).toFloat / 10000.0
    w2 := w2.push (r * scale2 - scale2/2)

  let mut b2 : Array Float := Array.mkEmpty 10
  for _ in [0:10] do
    b2 := b2.push 0.0

  pure { w1 := w1, b1 := b1, w2 := w2, b2 := b2 }

-- Compute accuracy on a batch
def computeAccuracy (weights : MLPWeights) (images labels : Array (Array Float)) : Float := Id.run do
  let mut correct : Nat := 0
  for idx in [0:images.size] do
    let pred := forward weights images[idx]!
    let label := labels[idx]!
    -- Find argmax of prediction and label
    let mut predMaxVal : Float := 0
    let mut labelMaxVal : Float := 0
    let mut predMaxIdx : Nat := 0
    let mut labelMaxIdx : Nat := 0
    for j in [0:10] do
      if pred[j]! > predMaxVal then
        predMaxVal := pred[j]!
        predMaxIdx := j
      if label[j]! > labelMaxVal then
        labelMaxVal := label[j]!
        labelMaxIdx := j
    if predMaxIdx = labelMaxIdx then
      correct := correct + 1
  correct.toFloat / images.size.toFloat

-- Training loop
def train (weights : MLPWeights) (trainImages trainLabels : Array (Array Float))
    (epochs : Nat) (lr : Float) : IO MLPWeights := do
  let mut w := weights
  let numSamples := min trainImages.size trainLabels.size

  for epoch in [0:epochs] do
    let mut totalLoss : Float := 0

    -- Mini-batch SGD (batch size = 1 for simplicity)
    for idx in [0:numSamples] do
      let x := trainImages[idx]!
      let y := trainLabels[idx]!

      -- Forward pass to get loss
      let loss := sampleLoss w x y
      totalLoss := totalLoss + loss

      -- Compute gradient (backprop) and update
      let grad := backprop w x y
      w := sgdUpdate w grad lr

      -- Progress indicator every 100 samples
      if idx % 100 = 99 then
        IO.print "."

    let avgLoss := totalLoss / numSamples.toFloat
    let accuracy := computeAccuracy w trainImages trainLabels
    IO.println s!"\nEpoch {epoch + 1}: avg_loss = {avgLoss}, train_acc = {accuracy * 100}%"

  return w

/-! ## Main -/

def main : IO Unit := do
  IO.println "Simple Feedforward Neural Network for MNIST"
  IO.println "==========================================="

  -- Load training data
  let numTrain := 1000  -- Using 1000 samples for reasonable speed
  let trainImages ← loadImages "data/train-images-idx3-ubyte" numTrain
  let trainLabels ← loadLabels "data/train-labels-idx1-ubyte" numTrain

  IO.println s!"Loaded {trainImages.size} training samples"

  -- Initialize weights
  IO.print "Initializing weights... "
  let weights ← initWeights
  IO.println "done"

  -- Initial accuracy (should be ~10% random)
  let initAcc := computeAccuracy weights trainImages trainLabels
  IO.println s!"Initial accuracy: {initAcc * 100}%"

  -- Train
  IO.println "\nTraining with analytical gradients..."
  let finalWeights ← train weights trainImages trainLabels 10 0.01

  -- Final accuracy
  let finalAcc := computeAccuracy finalWeights trainImages trainLabels
  IO.println s!"\nFinal accuracy: {finalAcc * 100}%"

  IO.println "\nDone!"
