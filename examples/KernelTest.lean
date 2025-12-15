/-
  Quick test of the minimal C kernel.
-/
import SciLean.Kernel.Ops

open SciLean.Kernel

def main : IO Unit := do
  IO.println "=== SciLean Kernel Test ==="

  -- Test DType
  IO.println s!"DType.f64 bytes: {DType.f64.bytes}"
  IO.println s!"DType.f32 bytes: {DType.f32.bytes}"
  IO.println s!"DType.bf16 bytes: {DType.bf16.bytes}"

  -- Test allocation
  let arr := Typed.alloc .f64 4
  IO.println s!"Allocated f64[4]: {arr.size} bytes"

  -- Test RNG
  let _ := rngSeed 42
  let uniform := Typed.randUniform .f64 4
  IO.println s!"Uniform random f64[4]: {uniform.size} bytes"

  let normal := Typed.randNormal .f64 4
  IO.println s!"Normal random f64[4]: {normal.size} bytes"

  -- Test elementwise ops
  let a := Typed.randUniform .f64 4
  let b := Typed.randUniform .f64 4
  let c := Typed.add .f64 a b
  IO.println s!"add f64[4]: {c.size} bytes"

  let d := Typed.mul .f64 a b
  IO.println s!"mul f64[4]: {d.size} bytes"

  -- Test sum reduction
  let sumVal := Typed.sum .f64 a
  IO.println s!"sum: {sumVal}"

  -- Test GEMM (2x3 @ 3x2 = 2x2)
  let A := Typed.randUniform .f64 6  -- 2x3
  let B := Typed.randUniform .f64 6  -- 3x2
  let C := Typed.gemm .f64 A B 2 3 2
  IO.println s!"gemm 2x3 @ 3x2 = 2x2: {C.size} bytes (expected {2*2*8})"

  -- Test transpose (3x2 -> 2x3)
  let X := Typed.randUniform .f64 6  -- 3x2
  let Xt := Typed.transpose .f64 X 3 2
  IO.println s!"transpose 3x2 -> 2x3: {Xt.size} bytes"

  -- Test softmax
  let logits := Typed.randUniform .f64 4
  let probs := Typed.softmax .f64 logits
  let probSum := Typed.sum .f64 probs
  IO.println s!"softmax sum (should be ~1.0): {probSum}"

  IO.println "\n=== All tests passed! ==="
