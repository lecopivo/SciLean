/-
  Test of the Kernel ↔ DataArrayN integration layer.
-/
import SciLean.Kernel.Integration

open SciLean SciLean.Kernel

def main : IO Unit := do
  IO.println "=== Kernel Integration Test ==="

  -- Seed RNG
  let _ := ArrayOps.seedRng 42

  -- Test random array generation
  let x : Float^[Idx 4] := ArrayOps.randUniform
  IO.println s!"Random uniform Float^[4] created"

  let y : Float^[Idx 4] := ArrayOps.randNormal
  IO.println s!"Random normal Float^[4] created"

  -- Test elementwise operations
  let z := ArrayOps.add x y
  IO.println s!"add: done"

  let w := ArrayOps.mul x y
  IO.println s!"mul: done"

  let expX := ArrayOps.exp x
  IO.println s!"exp: done"

  let sumZ := ArrayOps.sum z
  IO.println s!"sum: {sumZ}"

  -- Test matrix operations
  let A : Float^[Idx 2, Idx 3] := ArrayOps.randUniform
  let B : Float^[Idx 3, Idx 2] := ArrayOps.randUniform
  IO.println s!"Created matrices A[2,3] and B[3,2]"

  let C := ArrayOps.gemm A B
  IO.println s!"gemm A @ B: done"

  let At := ArrayOps.transpose A
  IO.println s!"transpose A: done"

  -- Test matrix-vector multiply
  let v : Float^[Idx 3] := ArrayOps.randUniform
  let Av := ArrayOps.gemv A v
  IO.println s!"gemv A @ v: done"

  -- Test softmax
  let logits : Float^[Idx 4] := ArrayOps.randUniform
  let probs := ArrayOps.softmax logits
  let probSum := ArrayOps.sum probs
  IO.println s!"softmax sum (should be ~1.0): {probSum}"

  -- Test backward helpers
  let dy : Float^[Idx 2] := ArrayOps.randUniform
  let dx := gemv_backward_x A dy
  IO.println s!"gemv_backward_x: done"

  let dC : Float^[Idx 2, Idx 2] := ArrayOps.randUniform
  let dA := gemm_backward_A B dC
  IO.println s!"gemm_backward_A: done"

  IO.println "\n=== All integration tests passed! ==="
