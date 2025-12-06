import SciLean.FFI.Metal
import SciLean.FFI.Float32Array

open SciLean

-- Check if GEMM result is correct using reduceSum
-- For all-ones matrices: C = A * B should have all entries = k, so sum = m*n*k
def checkGemm (name : String) (gemm : USize → USize → USize → ByteArray → ByteArray → ByteArray) (n : Nat) : IO Unit := do
  let amat := Metal.Float32.fill (n * n).toUSize (1.0 : Float32)
  let bmat := Metal.Float32.fill (n * n).toUSize (1.0 : Float32)
  let cmat := gemm n.toUSize n.toUSize n.toUSize amat bmat

  -- Check first element: C[0,0] should be n (dot product of n ones = n)
  -- Read first 4 bytes and decode as Float32
  let b0 := cmat.get! 0
  let b1 := cmat.get! 1
  let b2 := cmat.get! 2
  let b3 := cmat.get! 3
  let bits : UInt32 := b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)

  -- C should be n×n matrix with all entries = n, so sum = n*n*n = n³
  let expectedSum := (n * n * n).toFloat
  let actualSumF32 := Metal.Float32.reduceSum (n * n).toUSize cmat
  let actualSum := actualSumF32.toFloat

  let relError := if expectedSum > 0 then (actualSum - expectedSum).abs / expectedSum else actualSum.abs

  if relError < 0.01 then
    IO.println s!"  {name}: CORRECT (sum = {actualSum}, expected = {expectedSum}, C[0,0] bits = {bits})"
  else
    IO.println s!"  {name}: FAILED (sum = {actualSum}, expected = {expectedSum}, error = {relError * 100}%, C[0,0] bits = {bits})"

def main : IO Unit := do
  IO.println "=== GEMM Correctness Check ==="
  IO.println "Computing C = A * B where A, B are all 1s\n"

  -- First, test that fill works
  IO.println "Testing fill(4, 1.0)..."
  let testFill := Metal.Float32.fill 4 (1.0 : Float32)
  IO.println s!"  Fill result size: {testFill.size} bytes"
  IO.println s!"  Fill bytes: [{testFill.get! 0}, {testFill.get! 1}, {testFill.get! 2}, {testFill.get! 3}]"
  IO.println ""

  for n in [4, 8, 64] do
    IO.println s!"Matrix size: {n}×{n}"
    checkGemm "M4Pro      " Metal.Float32.gemmM4Pro n
    checkGemm "MPS        " Metal.Float32.gemmMPS n
    checkGemm "Accelerate " Metal.Float32.gemmAccelerate n
    IO.println ""

  IO.println "Done!"
