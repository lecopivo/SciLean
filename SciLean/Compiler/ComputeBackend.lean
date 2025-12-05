import SciLean.FFI.Metal
import SciLean.Compiler.LazyTensor

/-!
# Compute Backend Abstraction

A unified interface for tensor operations that can be dispatched to different backends:
- **CPU**: Pure Lean implementation using FloatArray
- **Metal**: GPU-accelerated via Apple Metal (macOS/iOS)
- **CUDA**: GPU-accelerated via NVIDIA CUDA (future)

This enables LazyTensor to execute on the best available backend.
-/

namespace SciLean.Compiler

/-! ## Backend Selection -/

/-- Available compute backends. -/
inductive Backend where
  | cpu    : Backend
  | metal  : Backend
  deriving Repr, BEq

/-- Detect the best available backend. -/
def Backend.detect : Backend :=
  if Metal.isAvailable () then .metal else .cpu

/-- Current active backend (uses auto-detection). -/
def Backend.current : Backend := Backend.detect

/-! ## Backend Operations Interface

These functions dispatch to the appropriate backend based on `Backend.current`.
-/

namespace BackendOps

/-- Fill array with constant value. -/
def fill (n : Nat) (value : Float) : FloatArray :=
  match Backend.current with
  | .metal => Metal.fill n.toUSize value
  | .cpu =>
    Id.run do
      let mut arr := FloatArray.empty
      for _ in [:n] do
        arr := arr.push value
      return arr

/-- Element-wise negation. -/
def neg (x : FloatArray) : FloatArray :=
  let n := x.size
  match Backend.current with
  | .metal => Metal.neg n.toUSize x
  | .cpu => FloatArray.mk (x.data.map (- ·))

/-- Element-wise exp2. -/
def exp2 (x : FloatArray) : FloatArray :=
  let n := x.size
  match Backend.current with
  | .metal => Metal.exp2 n.toUSize x
  | .cpu => FloatArray.mk (x.data.map fun v => Float.exp (v * Float.log 2))

/-- Element-wise log2. -/
def log2 (x : FloatArray) : FloatArray :=
  let n := x.size
  match Backend.current with
  | .metal => Metal.log2 n.toUSize x
  | .cpu => FloatArray.mk (x.data.map fun v => Float.log v / Float.log 2)

/-- Element-wise sin. -/
def sin (x : FloatArray) : FloatArray :=
  let n := x.size
  match Backend.current with
  | .metal => Metal.sin n.toUSize x
  | .cpu => FloatArray.mk (x.data.map Float.sin)

/-- Element-wise sqrt. -/
def sqrt (x : FloatArray) : FloatArray :=
  let n := x.size
  match Backend.current with
  | .metal => Metal.sqrt n.toUSize x
  | .cpu => FloatArray.mk (x.data.map Float.sqrt)

/-- Element-wise reciprocal. -/
def reciprocal (x : FloatArray) : FloatArray :=
  let n := x.size
  match Backend.current with
  | .metal => Metal.reciprocal n.toUSize x
  | .cpu => FloatArray.mk (x.data.map (1.0 / ·))

/-- Element-wise addition. -/
def add (x y : FloatArray) : FloatArray :=
  let n := x.size
  match Backend.current with
  | .metal => Metal.add n.toUSize x y
  | .cpu => FloatArray.mk (Array.zipWith (· + ·) x.data y.data)

/-- Element-wise subtraction. -/
def sub (x y : FloatArray) : FloatArray :=
  let n := x.size
  match Backend.current with
  | .metal => Metal.sub n.toUSize x y
  | .cpu => FloatArray.mk (Array.zipWith (· - ·) x.data y.data)

/-- Element-wise multiplication. -/
def mul (x y : FloatArray) : FloatArray :=
  let n := x.size
  match Backend.current with
  | .metal => Metal.mul n.toUSize x y
  | .cpu => FloatArray.mk (Array.zipWith (· * ·) x.data y.data)

/-- Element-wise division. -/
def div (x y : FloatArray) : FloatArray :=
  let n := x.size
  match Backend.current with
  | .metal => Metal.div n.toUSize x y
  | .cpu => FloatArray.mk (Array.zipWith (· / ·) x.data y.data)

/-- Element-wise maximum. -/
def max (x y : FloatArray) : FloatArray :=
  let n := x.size
  match Backend.current with
  | .metal => Metal.max n.toUSize x y
  | .cpu => FloatArray.mk (Array.zipWith (fun a b => if a >= b then a else b) x.data y.data)

/-- Element-wise minimum. -/
def min (x y : FloatArray) : FloatArray :=
  let n := x.size
  match Backend.current with
  | .metal => Metal.min n.toUSize x y
  | .cpu => FloatArray.mk (Array.zipWith (fun a b => if a <= b then a else b) x.data y.data)

/-- Reduce sum. -/
def reduceSum (x : FloatArray) : Float :=
  let n := x.size
  match Backend.current with
  | .metal => Metal.reduceSum n.toUSize x
  | .cpu => x.data.foldl (· + ·) 0.0

/-- Reduce max. -/
def reduceMax (x : FloatArray) : Float :=
  let n := x.size
  match Backend.current with
  | .metal => Metal.reduceMax n.toUSize x
  | .cpu => x.data.foldl (fun a b => if a >= b then a else b) (-1.0e308)

/-- Reduce min. -/
def reduceMin (x : FloatArray) : Float :=
  let n := x.size
  match Backend.current with
  | .metal => Metal.reduceMin n.toUSize x
  | .cpu => x.data.foldl (fun a b => if a <= b then a else b) 1.0e308

-- Matrix multiply: C = A @ B, where A is (m,k) and B is (k,n).
def gemm (m k n : Nat) (A B : FloatArray) : FloatArray :=
  match Backend.current with
  | .metal => Metal.gemm m.toUSize k.toUSize n.toUSize A B
  | .cpu =>
    Id.run do
      let mut result := FloatArray.empty
      for i in [:m] do
        for j in [:n] do
          let mut sum : Float := 0.0
          for l in [:k] do
            sum := sum + A.data[i * k + l]! * B.data[l * n + j]!
          result := result.push sum
      return result

end BackendOps

/-! ## Backend-Aware Interpreter

This interpreter uses the compute backend for all operations.
-/

namespace BackendInterpreter

/-- Apply a unary operation using the backend. -/
def applyUnary (op : UnaryOp) (x : RTensor) : RTensor :=
  let newData := match op with
    | .neg => BackendOps.neg x.data
    | .exp2 => BackendOps.exp2 x.data
    | .log2 => BackendOps.log2 x.data
    | .sin => BackendOps.sin x.data
    | .sqrt => BackendOps.sqrt x.data
    | .reciprocal => BackendOps.reciprocal x.data
    | .cast _ => x.data  -- No-op for Float-only
  { data := newData, shape := x.shape }

/-- Apply a binary operation using the backend (same shape only). -/
def applyBinarySameShape (op : BinaryOp) (x y : RTensor) : RTensor :=
  let newData := match op with
    | .add => BackendOps.add x.data y.data
    | .sub => BackendOps.sub x.data y.data
    | .mul => BackendOps.mul x.data y.data
    | .div => BackendOps.div x.data y.data
    | .max => BackendOps.max x.data y.data
    | .min => BackendOps.min x.data y.data
    | .cmpLt => FloatArray.mk (Array.zipWith (fun a b => if a < b then 1.0 else 0.0) x.data.data y.data.data)
    | .cmpEq => FloatArray.mk (Array.zipWith (fun a b => if a == b then 1.0 else 0.0) x.data.data y.data.data)
    | .matmul => panic! "matmul should be handled separately"
  { data := newData, shape := x.shape }

/-- Matrix multiplication using the backend. -/
def matmul (x y : RTensor) : RTensor :=
  let m := x.shape.getD 0 1
  let k := x.shape.getD 1 1
  let n := y.shape.getD 1 1
  let result := BackendOps.gemm m k n x.data y.data
  { data := result, shape := #[m, n] }

/-- Interpret a LazyNode using the compute backend. -/
partial def interpret (state : InterpState) (node : LazyNode) : RTensor :=
  match node with
  | .buffer id _ _ =>
    state.buffers.getD id (RTensor.ofConst 0.0 #[])

  | .const value shape _ =>
    match sintToShape shape with
    | some s =>
      let data := BackendOps.fill (s.foldl (· * ·) 1) value
      { data := data, shape := s }
    | none => panic! "Cannot interpret symbolic shape"

  | .unary op x =>
    let xVal := interpret state x
    applyUnary op xVal

  | .binary .matmul x y =>
    let xVal := interpret state x
    let yVal := interpret state y
    matmul xVal yVal

  | .binary op x y =>
    let xVal := interpret state x
    let yVal := interpret state y
    if xVal.shape == yVal.shape then
      applyBinarySameShape op xVal yVal
    else
      -- Fall back to CPU interpreter for broadcasting
      Interpreter.applyBinary op xVal yVal

  | .reduce op axes x =>
    let xVal := interpret state x
    -- For now, fall back to CPU for multi-axis reduce
    -- TODO: Implement proper GPU reduction
    Interpreter.applyReduce op axes xVal

  | .movement mop x =>
    let xVal := interpret state x
    match mop with
    | .reshape newShape =>
      match sintToShape newShape with
      | some s => Interpreter.reshape s xVal
      | none => panic! "Cannot interpret symbolic shape"
    | .permute perm => Interpreter.permute perm xVal
    | .expand _ => xVal  -- Handled by broadcasting
    | _ => panic! "Movement op not yet implemented"

end BackendInterpreter

/-! ## High-Level API -/

/-- Execute a lazy tensor using the best available backend. -/
def LazyTensor.runWithBackend (buffers : BufferStore := []) (t : LazyTensor) : RTensor :=
  let node := t.realize
  BackendInterpreter.interpret { buffers := buffers } node

/-- Print current backend status. -/
def printBackendStatus : IO Unit := do
  match Backend.current with
  | .metal => IO.println "Compute Backend: Metal GPU"
  | .cpu => IO.println "Compute Backend: CPU"

end SciLean.Compiler
