/-
Test DataArrayN operations to identify sorry_proof panics
-/
import SciLean

open SciLean

set_default_scalar Float

def main : IO Unit := do
  IO.println "Testing DataArrayN operations..."

  -- Test 1: Create a simple Float^[5]
  IO.print "Test 1: Creating Float^[5] with ⊞ notation... "
  let arr1 : Float^[5] := ⊞ (i : Idx 5) => i.1.toFloat
  IO.println s!"OK: {arr1}"

  -- Test 2: Create Float^[2,3] matrix
  IO.print "Test 2: Creating Float^[2,3] matrix... "
  let arr2 : Float^[2, 3] := ⊞ (ij : Idx 2 × Idx 3) => (ij.1.1 + ij.2.1).toFloat
  IO.println s!"OK: first elem = {arr2[⟨0, by decide⟩, ⟨0, by decide⟩]}"

  -- Test 3: Element access
  IO.print "Test 3: Element access... "
  let _ := arr1[⟨0, by decide⟩]
  IO.println "OK"

  -- Test 4: mapMono
  IO.print "Test 4: mapMono (x => x * 2)... "
  let arr3 := arr1.mapMono (· * 2)
  IO.println s!"OK: {arr3}"

  -- Test 5: Addition
  IO.print "Test 5: Array addition... "
  let arr4 := arr1 + arr1
  IO.println s!"OK: {arr4}"

  -- Test 6: contractRightAddR (matrix-vector multiply)
  IO.print "Test 6: Matrix-vector multiply... "
  let mat : Float^[2, 3] := ⊞ (_ : Idx 2 × Idx 3) => 1.0
  let vec : Float^[3] := ⊞ (_ : Idx 3) => 1.0
  let bias : Float^[2] := 0
  let result := DataArrayN.contractRightAddR 1.0 mat vec 1.0 bias
  IO.println s!"OK: {result}"

  -- Test 7: softmax
  IO.print "Test 7: softmax... "
  let logits : Float^[5] := ⊞ (i : Idx 5) => i.1.toFloat
  let probs := DataArrayN.softmax logits
  IO.println s!"OK: {probs}"

  -- Test 8: outerAddR
  IO.print "Test 8: outerAddR... "
  let u : Float^[2] := ⊞ (_ : Idx 2) => 1.0
  let v : Float^[3] := ⊞ (_ : Idx 3) => 2.0
  let outer := DataArrayN.outerAddR 1.0 u v 0
  IO.println s!"OK: {outer}"

  IO.println "\nAll tests passed!"
