/-
Test .npy roundtrip: Load arrays from Python, verify values match.
-/
import SciLean
import SciLean.Data.Npy
import SciLean.Data.DataArray.TensorOperations

open SciLean

def almostEq (a b : Float) (tol : Float := 1e-10) : Bool :=
  (a - b).abs < tol

def main : IO Unit := do
  IO.println "=== Testing .npy Roundtrip ==="
  IO.println ""

  -- Test 1: Load 1D array
  IO.println "Test 1: Load 1D array"
  let arr1d ← Npy.loadFile "data/npy_test/test_1d.npy"
  IO.println s!"  dtype: {repr arr1d.dtype}, shape: {repr arr1d.shape.dims}"
  let floats1d ← IO.ofExcept arr1d.toFloatArray
  IO.print "  values: ["
  for i in [0:floats1d.size] do
    if i > 0 then IO.print ", "
    IO.print s!"{floats1d.uget i.toUSize sorry_proof}"
  IO.println "]"
  let sum1d := (List.range floats1d.size).foldl (fun acc i =>
    acc + floats1d.uget i.toUSize sorry_proof) 0.0
  IO.println s!"  sum: {sum1d} (expected: 15.0)"
  if almostEq sum1d 15.0 then
    IO.println "  ✓ PASS"
  else
    IO.println "  ✗ FAIL"

  -- Test 2: Load 2D array as flat
  IO.println ""
  IO.println "Test 2: Load 2D array (3x4)"
  let arr2d ← Npy.loadFile "data/npy_test/test_2d.npy"
  IO.println s!"  dtype: {repr arr2d.dtype}, shape: {repr arr2d.shape.dims}"
  let floats2d ← IO.ofExcept arr2d.toFloatArray
  let sum2d := (List.range floats2d.size).foldl (fun acc i =>
    acc + floats2d.uget i.toUSize sorry_proof) 0.0
  IO.println s!"  sum: {sum2d} (expected: 66.0)"
  if almostEq sum2d 66.0 then
    IO.println "  ✓ PASS"
  else
    IO.println "  ✗ FAIL"

  -- Test 3: Matrix-vector multiply
  IO.println ""
  IO.println "Test 3: Matrix-vector multiply"
  let arrA ← Npy.loadFile "data/npy_test/test_A.npy"
  let arrX ← Npy.loadFile "data/npy_test/test_x.npy"
  let arrY ← Npy.loadFile "data/npy_test/test_y.npy"
  IO.println s!"  A shape: {repr arrA.shape.dims}"
  IO.println s!"  x shape: {repr arrX.shape.dims}"
  IO.println s!"  y shape: {repr arrY.shape.dims}"

  -- Load as DataArrayN and compute
  let A : Float^[3, 2] ← Npy.loadFloat64 "data/npy_test/test_A.npy"
  let x : Float^[2] ← Npy.loadFloat64 "data/npy_test/test_x.npy"
  let expectedY : Float^[3] ← Npy.loadFloat64 "data/npy_test/test_y.npy"

  -- Compute y = A @ x using contractRightAddR
  let computedY : Float^[3] := DataArrayN.contractRightAddR 1.0 A x 0.0 0

  IO.println s!"  expected y: [{expectedY[⟨0, sorry_proof⟩]}, {expectedY[⟨1, sorry_proof⟩]}, {expectedY[⟨2, sorry_proof⟩]}]"
  IO.println s!"  computed y: [{computedY[⟨0, sorry_proof⟩]}, {computedY[⟨1, sorry_proof⟩]}, {computedY[⟨2, sorry_proof⟩]}]"

  let match0 := almostEq computedY[⟨0, sorry_proof⟩] expectedY[⟨0, sorry_proof⟩]
  let match1 := almostEq computedY[⟨1, sorry_proof⟩] expectedY[⟨1, sorry_proof⟩]
  let match2 := almostEq computedY[⟨2, sorry_proof⟩] expectedY[⟨2, sorry_proof⟩]

  if match0 && match1 && match2 then
    IO.println "  ✓ PASS"
  else
    IO.println "  ✗ FAIL"

  -- Test 4: Softmax
  IO.println ""
  IO.println "Test 4: Softmax"
  let logits : Float^[4] ← Npy.loadFloat64 "data/npy_test/test_logits.npy"
  let expectedSoftmax : Float^[4] ← Npy.loadFloat64 "data/npy_test/test_softmax.npy"

  -- Compute softmax using DataArrayN.softmax
  let computedSoftmax : Float^[4] := DataArrayN.softmax logits

  IO.println s!"  expected: [{expectedSoftmax[⟨0, sorry_proof⟩]}, {expectedSoftmax[⟨1, sorry_proof⟩]}, {expectedSoftmax[⟨2, sorry_proof⟩]}, {expectedSoftmax[⟨3, sorry_proof⟩]}]"
  IO.println s!"  computed: [{computedSoftmax[⟨0, sorry_proof⟩]}, {computedSoftmax[⟨1, sorry_proof⟩]}, {computedSoftmax[⟨2, sorry_proof⟩]}, {computedSoftmax[⟨3, sorry_proof⟩]}]"

  let softmaxMatch := almostEq computedSoftmax[⟨0, sorry_proof⟩] expectedSoftmax[⟨0, sorry_proof⟩] 1e-6
                   && almostEq computedSoftmax[⟨1, sorry_proof⟩] expectedSoftmax[⟨1, sorry_proof⟩] 1e-6
                   && almostEq computedSoftmax[⟨2, sorry_proof⟩] expectedSoftmax[⟨2, sorry_proof⟩] 1e-6
                   && almostEq computedSoftmax[⟨3, sorry_proof⟩] expectedSoftmax[⟨3, sorry_proof⟩] 1e-6

  if softmaxMatch then
    IO.println "  ✓ PASS"
  else
    IO.println "  ✗ FAIL"

  IO.println ""
  IO.println "=== All tests completed ==="
