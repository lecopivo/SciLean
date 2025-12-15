import SciLean
/-

# Numpy-100 Exercises in SciLean

This demonstrates the high-level DataArrayN API with Float^[n] notation.
Metal GPU acceleration happens transparently underneath.

Reference: https://github.com/rougier/numpy-100
-/

open SciLean

set_default_scalar Float

-- Exercise 3: Create a zero vector of size 10
def exercise3 : Float^[10] := 0

-- Exercise 6: Build a null vector (size 10) with fifth element set to 1
def exercise6 : Float^[10] := Id.run do
  let mut z : Float^[10] := 0
  z[(4 : Idx 10)] := 1.0
  return z

-- Exercise 7: Generate a vector containing values from 10 to 49
def exercise7 : Float^[40] := DataArrayN.arange 40 (start := 10)

-- Exercise 8: Reverse a vector (first element becomes last)
def exercise8 {n : Nat} (v : Float^[n]) : Float^[n] :=
  v.reverse

-- Exercise 9: Build a 3x3 matrix with sequential values 0-8
def exercise9 : Float^[3, 3] :=
  (DataArrayN.arange 9).reshape2 3 3 (by decide)

-- Exercise 10: Find indices of non-zero elements from [1,2,0,0,4,0]
def exercise10 : Array (Idx 6) :=
  (⊞[1.0, 2.0, 0.0, 0.0, 4.0, 0.0] : Float^[6]).nonzeroIdx

-- Exercise 11: Generate a 3x3 identity matrix
def exercise11 : Float^[3, 3] := DataArrayN.eye 3

-- Exercise 13: Make a random array and identify min/max
-- Note: SciLean doesn't have random by default, using deterministic example
def exercise13_demo : IO Unit := do
  let arr : Float^[10, 10] := (DataArrayN.arange 100).reshape2 10 10 (by decide)
  let minVal := arr.rmin
  let maxVal := arr.rmax
  IO.println s!"Min: {minVal}, Max: {maxVal}"

-- Exercise 14: Generate a vector and compute its mean
def exercise14 : IO Unit := do
  let arr : Float^[30] := DataArrayN.arange 30
  IO.println s!"Mean: {arr.mean}"

-- Exercise 22: Normalize a 5x5 matrix
def normalizeMatrix (m n : Nat) (arr : Float^[m, n]) : Float^[m, n] :=
  let minVal := arr.rmin
  let maxVal := arr.rmax
  let range := maxVal - minVal
  arr.map (fun x => (x - minVal) / range)

-- Exercise 24: Multiply 5x3 by 3x2 matrices
def exercise24 : IO Unit := do
  let A : Float^[5, 3] := ⊞ (i : Idx 5) (j : Idx 3) => ((i : Nat) + (j : Nat)).toFloat
  let B : Float^[3, 2] := ⊞ (i : Idx 3) (j : Idx 2) => ((i : Nat) * (j : Nat)).toFloat
  let C := A.matmul B
  IO.println s!"C[0,0] = {C[0,0]}"

-- Exercise 37: Create 5x5 matrix with row values from 0-4
def exercise37 : Float^[5, 5] := ⊞ (_i : Idx 5) (j : Idx 5) => (j : Nat).toFloat

-- Exercise 38: Build array from generator producing integers
def exercise38 : Float^[10] := ⊞ (i : Idx 10) => ((i : Nat) * (i : Nat)).toFloat  -- squares

-- Exercise 45: Replace maximum value with 0
def exercise45 (n : Nat) (v : Float^[n]) : Float^[n] :=
  let maxVal := v.rmax
  v.map (fun x => if x == maxVal then 0.0 else x)

-- Exercise 58: Subtract row means from matrix
def exercise58 (m n : Nat) (A : Float^[m, n]) : Float^[m, n] :=
  ⊞ (i : Idx m) (j : Idx n) =>
    let rowSum := IndexType.sum (fun (k : Idx n) => A[i, k])
    let rowMean := rowSum / n.toFloat
    A[i, j] - rowMean

-- Exercise 82: Calculate matrix rank (via determinant for now)
-- Note: Proper rank calculation would need SVD
def matrixDet (n : Nat) (A : Float^[n, n]) : Float := A.det

-- Exercise 83: Find most frequent value (integer version)
def mostFrequent (n : Nat) [NeZero n] (v : Float^[n]) : Float :=
  -- Simple O(n²) implementation
  let counts : Float^[n] := ⊞ (i : Idx n) =>
    IndexType.sum (fun (j : Idx n) => if v[i] == v[j] then 1.0 else 0.0)
  let maxIdx : Idx n := counts.argmax
  v[maxIdx]

-- Neural network style operations (common in numpy ML)

-- Softmax (normalized exponential)
def softmax' (n : Nat) (x : Float^[n]) : Float^[n] := x.softmax

-- ReLU activation
def reluActivation (n : Nat) (x : Float^[n]) : Float^[n] := x.rmap (fun v => max 0.0 v)

-- Sigmoid activation
def sigmoidActivation (n : Nat) (x : Float^[n]) : Float^[n] := x.rmap (fun v => 1.0 / (1.0 + Float.exp (-v)))

-- BatchNorm (simplified - no learnable params)
def batchNorm (batchSize features : Nat) (x : Float^[batchSize, features]) (eps : Float := 1e-5)
    : Float^[batchSize, features] :=
  ⊞ (b : Idx batchSize) (f : Idx features) =>
    let mean := IndexType.sum (fun (i : Idx batchSize) => x[i, f]) / batchSize.toFloat
    let variance := IndexType.sum (fun (i : Idx batchSize) => (x[i, f] - mean)^2) / batchSize.toFloat
    (x[b, f] - mean) / Float.sqrt (variance + eps)

-- Linear layer: y = Wx + b
def linearLayer (outDim inpDim : Nat) (W : Float^[outDim, inpDim]) (b : Float^[outDim]) (x : Float^[inpDim])
    : Float^[outDim] :=
  let Wx := DataArrayN.contractRightAddR 1.0 W x 0.0 (0 : Float^[outDim])
  Wx + b

-- Dot product
def dotProd (n : Nat) (x y : Float^[n]) : Float :=
  IndexType.sum (fun (i : Idx n) => x[i] * y[i])

-- Cross product (3D only)
def cross (x y : Float^[3]) : Float^[3] :=
  ⊞ (i : Idx 3) =>
    let i1 := ((i : Nat) + 1) % 3
    let i2 := ((i : Nat) + 2) % 3
    x[⟨i1.toUSize, sorry_proof⟩] * y[⟨i2.toUSize, sorry_proof⟩] -
    x[⟨i2.toUSize, sorry_proof⟩] * y[⟨i1.toUSize, sorry_proof⟩]

-- Matrix transpose (through reshape/permute)
def transposeMatrix (m n : Nat) (A : Float^[m, n]) : Float^[n, m] :=
  ⊞ (j : Idx n) (i : Idx m) => A[i, j]

-- Trace of a square matrix
def traceMatrix (n : Nat) (A : Float^[n, n]) : Float :=
  IndexType.sum (fun (i : Idx n) => A[i, i])

-- Outer product
def outerProduct (m n : Nat) (x : Float^[m]) (y : Float^[n]) : Float^[m, n] :=
  ⊞ (i : Idx m) (j : Idx n) => x[i] * y[j]

-- Frobenius norm
def frobeniusNorm (m n : Nat) (A : Float^[m, n]) : Float :=
  Float.sqrt (IndexType.sum (fun (i : Idx m) => IndexType.sum (fun (j : Idx n) => A[i, j]^2)))

def main : IO Unit := do
  IO.println "=== Numpy-100 Exercises in SciLean ==="
  IO.println ""

  IO.println "Exercise 3: Create zero vector"
  IO.println s!"  {exercise3}"

  IO.println "\nExercise 6: Null vector with 5th element = 1"
  IO.println s!"  {exercise6}"

  IO.println "\nExercise 7: Vector from 10 to 49"
  let first5 : Float^[5] := DataArrayN.arange 5 (start := 10)
  IO.println s!"  First 5: {first5}"

  IO.println "\nExercise 10: Indices of non-zero elements from [1,2,0,0,4,0]"
  let idxsNat : Array Nat := exercise10.map (fun (i : Idx 6) => (i : Nat))
  IO.println s!"  {idxsNat}"

  IO.println "\nExercise 9: 3x3 matrix with 0-8"
  IO.println s!"  {exercise9}"

  IO.println "\nExercise 11: 3x3 identity matrix"
  IO.println s!"  {exercise11}"

  IO.println "\nExercise 24: Matrix multiply (5x3) @ (3x2)"
  exercise24

  IO.println "\nExercise 37: 5x5 matrix with row values 0-4"
  let rowVals := exercise37
  let row0 : Float^[5] := ⊞ (j : Idx 5) => rowVals[0, j]
  IO.println s!"  Row 0: {row0}"

  IO.println "\nNeural network operations:"

  let testVec : Float^[5] := DataArrayN.arange 5 (start := 1)
  IO.println s!"  Input: {testVec}"
  IO.println s!"  Softmax: {softmax' 5 testVec}"

  let reluInput : Float^[5] := DataArrayN.arange 5 (start := -2)
  IO.println s!"  ReLU of {reluInput}: {reluActivation 5 reluInput}"

  IO.println "\nLinear algebra:"
  let v1 : Float^[3] := ⊞ (i : Idx 3) => if i.1 == 0 then 1.0 else 0.0
  let v2 : Float^[3] := ⊞ (i : Idx 3) => if i.1 == 1 then 1.0 else 0.0
  IO.println s!"  Cross product [1,0,0] x [0,1,0]: {cross v1 v2}"
  let dotV : Float^[3] := DataArrayN.arange 3 (start := 1)
  IO.println s!"  Dot product [1,2,3] . [1,2,3]: {dotProd 3 dotV dotV}"

  let testMat : Float^[2, 2] :=
    ⊞ (i : Idx 2) (j : Idx 2) => (((i : Nat) * 2 + (j : Nat) + 1) : Nat).toFloat
  IO.println s!"  Matrix [[1,2],[3,4]]:"
  IO.println s!"  Trace: {traceMatrix 2 testMat}"
  IO.println s!"  Det: {matrixDet 2 testMat}"
  IO.println s!"  Frobenius norm: {frobeniusNorm 2 2 testMat}"

  IO.println "\n=== Done ==="
