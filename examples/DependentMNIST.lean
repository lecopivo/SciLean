/-
Dependently-Typed MNIST Neural Network

A type-safe 2-layer MLP classifier using DataArrayN:
  Input:  Float^[784]  (28×28 flattened)
  Hidden: Float^[128]  with GELU activation
  Output: Float^[10]   with softmax

The dependent types guarantee dimensional correctness at compile time.
-/
import SciLean

open SciLean Scalar ArrayType.PowerNotation

set_default_scalar Float

/-! ## Data Loading -/

def checkFileExists (path : System.FilePath) : IO Unit := do
  if ¬(← path.pathExists) then
     throw (IO.userError s!"MNIST data file '{path}' not found. Please download from https://git-disl.github.io/GTDLBench/datasets/mnist_datasets/")

/-- Load MNIST images as dependently-typed `Float^[784]` arrays -/
def loadImages (path : System.FilePath) (maxImages : Nat) : IO (Array (Float^[784])) := do
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

  -- Convert to Float^[784] arrays
  let mut images : Array (Float^[784]) := #[]
  for bytes in data do
    -- Create Float^[784] using ⊞ notation
    let img : Float^[784] := ⊞ (i : Idx 784) =>
      let byteVal := bytes.get! i.1.toNat
      byteVal.toNat.toFloat / 255.0
    images := images.push img

  IO.println s!"done ({(← IO.monoMsNow) - start}ms)"
  return images

/-- Load MNIST labels as one-hot encoded `Float^[10]` arrays -/
def loadLabels (path : System.FilePath) (maxLabels : Nat) : IO (Array (Float^[10])) := do
  checkFileExists path
  if maxLabels = 0 then return #[]

  let start ← IO.monoMsNow
  IO.print s!"Loading labels from {path}... "

  let data ← IO.FS.withFile path .read fun m => do
    let _header ← m.read 8
    m.read maxLabels.toUSize

  if data.size ≠ maxLabels then
    throw <| IO.userError s!"File {path} contains only {data.size} labels"

  -- Convert to one-hot encoded Float^[10]
  let mut labels : Array (Float^[10]) := #[]
  for b in data do
    let labelIdx := b.toNat
    let label : Float^[10] := ⊞ (i : Idx 10) =>
      if i.1.toNat = labelIdx then 1.0 else 0.0
    labels := labels.push label

  IO.println s!"done ({(← IO.monoMsNow) - start}ms)"
  return labels

/-! ## Activation Functions -/

/-- GELU activation (Gaussian Error Linear Unit) -/
def gelu (x : Float) : Float :=
  let pi : Float := 3.141592653589793
  let c := Float.sqrt (2.0 / pi)
  x * (1 + Float.tanh (c * x * (1 + 0.044715 * x^2)))

/-! ## Network Definition with Dependent Types -/

/-- Network weights with type-safe dimensions -/
structure Weights where
  w1 : Float^[128, 784]   -- First layer: 128 neurons, 784 inputs
  b1 : Float^[128]        -- First layer bias
  w2 : Float^[10, 128]    -- Second layer: 10 outputs, 128 inputs
  b2 : Float^[10]         -- Second layer bias

/--
Forward pass with type-guaranteed dimensions.

The types enforce:
- Input must be 784-dimensional
- Output is guaranteed 10-dimensional
- Hidden layer is 128-dimensional (internal)
-/
def forward (x : Float^[784]) (w : Weights) : Float^[10] :=
  -- Hidden layer: h = gelu(W1 * x + b1)
  -- Using contractRightAddR: computes a*W*x + b*z
  let h1 : Float^[128] := DataArrayN.contractRightAddR 1.0 w.w1 x 1.0 w.b1
  -- Apply GELU activation element-wise
  let a1 : Float^[128] := h1.mapMono gelu

  -- Output layer: o = W2 * a1 + b2
  let h2 : Float^[10] := DataArrayN.contractRightAddR 1.0 w.w2 a1 1.0 w.b2

  -- Softmax for probabilities
  DataArrayN.softmax h2

/-- Cross-entropy loss between prediction and target -/
def crossEntropyLoss (pred actual : Float^[10]) : Float :=
  let eps : Float := 1e-7
  ∑ᴵ (i : Idx 10), - actual[i] * Scalar.log (pred[i] + eps)

/-- Compute loss for a single sample -/
def sampleLoss (w : Weights) (x : Float^[784]) (y : Float^[10]) : Float :=
  crossEntropyLoss (forward x w) y

/-! ## Gradient Computation (Manual Backpropagation) -/

/-- Manual backpropagation returning weight gradients -/
def backprop (w : Weights) (x : Float^[784]) (y : Float^[10]) : Weights := Id.run do
  -- Forward pass with intermediate values stored
  let h_pre : Float^[128] := DataArrayN.contractRightAddR 1.0 w.w1 x 1.0 w.b1
  let h : Float^[128] := h_pre.mapMono gelu

  let o_pre : Float^[10] := DataArrayN.contractRightAddR 1.0 w.w2 h 1.0 w.b2
  let pred : Float^[10] := DataArrayN.softmax o_pre

  -- Backward pass
  -- dL/do = pred - actual (for softmax + cross-entropy)
  let d_o : Float^[10] := pred - y

  -- Gradients for w2 and b2
  -- dw2[i,j] = d_o[i] * h[j]
  let dw2 : Float^[10, 128] := DataArrayN.outerAddR 1.0 d_o h 0
  let db2 : Float^[10] := d_o

  -- Backprop through hidden layer: d_h = W2^T * d_o
  -- Using contractLeftAddR: computes a*x^T*W + b*z
  let d_h : Float^[128] := DataArrayN.contractLeftAddR 1.0 d_o w.w2 0.0 0

  -- Backprop through GELU activation (numerical derivative)
  let eps := 1e-4
  let d_h_pre : Float^[128] := d_h.mapIdxMono fun i dhi =>
    let xi := h_pre[i]
    let gelu_deriv := (gelu (xi + eps) - gelu (xi - eps)) / (2 * eps)
    dhi * gelu_deriv

  -- Gradients for w1 and b1
  -- dw1[i,j] = d_h_pre[i] * x[j]
  let dw1 : Float^[128, 784] := DataArrayN.outerAddR 1.0 d_h_pre x 0
  let db1 : Float^[128] := d_h_pre

  { w1 := dw1, b1 := db1, w2 := dw2, b2 := db2 }

/-! ## Training -/

/-- SGD update step -/
def sgdUpdate (w grad : Weights) (lr : Float) : Weights :=
  { w1 := w.w1 - lr • grad.w1
    b1 := w.b1 - lr • grad.b1
    w2 := w.w2 - lr • grad.w2
    b2 := w.b2 - lr • grad.b2 }

/-- Generate random Float in `[0,1)` -/
def rand01 : IO Float := do
  let N : Nat := 10^9
  let i ← IO.rand 0 N
  return i.toFloat / N.toFloat

/-- Initialize weights with He initialization -/
def initWeights : IO Weights := do
  let scale1 := Float.sqrt (2.0 / 784.0)
  let scale2 := Float.sqrt (2.0 / 128.0)

  -- Initialize w1 with random values scaled by He init
  -- Use FloatArray.push in IO monad for proper sequencing
  let mut w1Arr : FloatArray := .emptyWithCapacity (128 * 784)
  for _ in [0:128*784] do
    let r ← rand01
    w1Arr := w1Arr.push (r * scale1 - scale1/2)
  let w1 : Float^[128, 784] := DataArrayN.fromFloatArray w1Arr

  let b1 : Float^[128] := 0

  -- Initialize w2
  let mut w2Arr : FloatArray := .emptyWithCapacity (10 * 128)
  for _ in [0:10*128] do
    let r ← rand01
    w2Arr := w2Arr.push (r * scale2 - scale2/2)
  let w2 : Float^[10, 128] := DataArrayN.fromFloatArray w2Arr

  let b2 : Float^[10] := 0

  pure { w1 := w1, b1 := b1, w2 := w2, b2 := b2 }

/-- Compute accuracy on a batch -/
def computeAccuracy (w : Weights) (images : Array (Float^[784])) (labels : Array (Float^[10])) : Float := Id.run do
  let mut correct : Nat := 0
  for idx in [0:images.size] do
    let pred := forward images[idx]! w
    let label := labels[idx]!
    -- Use the new DataArrayN.argmax function
    let predMaxIdx := DataArrayN.argmax pred
    let labelMaxIdx := DataArrayN.argmax label
    if predMaxIdx = labelMaxIdx then
      correct := correct + 1
  correct.toFloat / images.size.toFloat

/-- Training loop -/
def train (w : Weights) (trainImages : Array (Float^[784])) (trainLabels : Array (Float^[10]))
    (epochs : Nat) (lr : Float) : IO Weights := do
  let mut w := w
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
  IO.println "Dependently-Typed MNIST Neural Network"
  IO.println "======================================="
  IO.println "Using SciLean DataArrayN with type-safe dimensions:"
  IO.println "  Input:  Float^[784]"
  IO.println "  Hidden: Float^[128]"
  IO.println "  Output: Float^[10]"
  IO.println ""

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
