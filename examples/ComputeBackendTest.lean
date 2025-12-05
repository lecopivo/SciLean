-- Test for ComputeBackend abstraction
import SciLean.Compiler.ComputeBackend

open SciLean.Compiler

-- Approximate float comparison (within epsilon)
def floatEq (a b : Float) (eps : Float := 1e-6) : Bool :=
  (a - b).abs < eps

def listFloatEq (xs ys : List Float) (eps : Float := 1e-6) : Bool :=
  xs.length == ys.length && (xs.zip ys).all fun (x, y) => floatEq x y eps

-- Test backend detection and operations
def main : IO Unit := do
  IO.println "=== Compute Backend Tests ==="
  IO.println ""

  -- Print detected backend
  printBackendStatus
  IO.println ""

  -- Test fill operation
  IO.println "Testing fill operation:"
  let filled := BackendOps.fill 5 3.14
  let fillOk := listFloatEq filled.data.toList [3.14, 3.14, 3.14, 3.14, 3.14]
  IO.println s!"  fill 5 3.14: {if fillOk then "PASS" else "FAIL"}"
  IO.println s!"    Result: {filled.data.toList}"

  -- Test negation
  IO.println ""
  IO.println "Testing negation:"
  let arr := FloatArray.mk #[1.0, 2.0, 3.0]
  let negated := BackendOps.neg arr
  let negOk := listFloatEq negated.data.toList [-1.0, -2.0, -3.0]
  IO.println s!"  neg [1,2,3]: {if negOk then "PASS" else "FAIL"}"
  IO.println s!"    Result: {negated.data.toList}"

  -- Test addition
  IO.println ""
  IO.println "Testing addition:"
  let a := FloatArray.mk #[1.0, 2.0, 3.0]
  let b := FloatArray.mk #[4.0, 5.0, 6.0]
  let sum := BackendOps.add a b
  let addOk := listFloatEq sum.data.toList [5.0, 7.0, 9.0]
  IO.println s!"  [1,2,3] + [4,5,6]: {if addOk then "PASS" else "FAIL"}"
  IO.println s!"    Result: {sum.data.toList}"

  -- Test reduce sum
  IO.println ""
  IO.println "Testing reduce sum:"
  let arr := FloatArray.mk #[1.0, 2.0, 3.0, 4.0]
  let total := BackendOps.reduceSum arr
  let sumOk := floatEq total 10.0
  IO.println s!"  sum [1,2,3,4]: {if sumOk then "PASS" else "FAIL"}"
  IO.println s!"    Result: {total}"

  -- Test matrix multiply
  IO.println ""
  IO.println "Testing matrix multiply (2x2 @ 2x2):"
  let matA := FloatArray.mk #[1.0, 2.0, 3.0, 4.0]  -- [[1,2],[3,4]]
  let matB := FloatArray.mk #[5.0, 6.0, 7.0, 8.0]  -- [[5,6],[7,8]]
  let matC := BackendOps.gemm 2 2 2 matA matB
  let expected := [19.0, 22.0, 43.0, 50.0]
  let gemmOk := listFloatEq matC.data.toList expected
  IO.println s!"  gemm 2x2 @ 2x2: {if gemmOk then "PASS" else "FAIL"}"
  IO.println s!"    Result: {matC.data.toList}"
  IO.println s!"    Expected: {expected}"

  IO.println ""
  IO.println "=== All tests complete ==="
