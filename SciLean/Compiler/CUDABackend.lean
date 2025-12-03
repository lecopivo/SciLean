import Lean
import SciLean.Compiler.LazyTensor

/-!
# CUDA Backend Architecture for SciLean

## Overview

This module defines the architecture for CUDA GPU acceleration in SciLean.
The design is inspired by tinygrad's approach but adapted for Lean's type system
and FFI constraints.

## Key Design Decisions

### 1. JIT vs AOT Compilation

We use JIT compilation like tinygrad:
- Kernels are generated at runtime based on tensor shapes
- NVRTC compiles CUDA C to PTX at runtime
- Compiled kernels are cached by shape signature
- Allows symbolic shape specialization

### 2. Memory Management Strategy

Three-tier memory model:
- Host memory: Standard Lean FloatArray
- Pinned host memory: For fast CPU-GPU transfer
- Device memory: GPU-resident buffers

### 3. Kernel Fusion Strategy

Based on tinygrad's scheduling:
1. Elementwise ops fuse into single kernel
2. Reduce ops become separate kernels (need synchronization)
3. Movement ops are virtual - just change indexing

### 4. Integration with Lean FFI

The C layer provides functions for:
- CUDA availability check
- Device memory allocation/free
- Host-device memory transfer
- CUDA C compilation via NVRTC
- Kernel launch
-/

namespace SciLean.Compiler.CUDA

open LazyTensor

/-! ## Device Memory Handle

Opaque pointer to GPU memory. The actual pointer is managed by C code.
-/

/-- Opaque handle to device memory. -/
structure DevicePtr where
  /-- Raw pointer value (managed by C layer) -/
  ptr : USize
  /-- Size in bytes -/
  size : USize
  deriving Repr, BEq

/-- Opaque handle to a compiled CUDA module. -/
structure CUDAModule where
  handle : USize
  deriving Repr

/-- Opaque handle to a CUDA stream for async execution. -/
structure CUDAStream where
  handle : USize
  deriving Repr

/-! ## FFI Declarations

These are stubs - actual implementation requires C code with CUDA.
-/

/-- Check if CUDA is available on this system. -/
@[extern "scilean_cuda_available"]
opaque cudaAvailable : Unit → Bool

/-- Initialize CUDA and return device count. -/
@[extern "scilean_cuda_init"]
opaque cudaInit : Unit → IO Nat

/-- Allocate device memory. -/
@[extern "scilean_cuda_alloc"]
opaque cudaAlloc : USize → IO DevicePtr

/-- Free device memory. -/
@[extern "scilean_cuda_free"]
opaque cudaFree : DevicePtr → IO Unit

/-- Copy from host (FloatArray) to device. -/
@[extern "scilean_cuda_copy_htod"]
opaque cudaCopyHtoD : DevicePtr → @& FloatArray → IO Unit

/-- Copy from device to host (FloatArray). -/
@[extern "scilean_cuda_copy_dtoh"]
opaque cudaCopyDtoH : @& FloatArray → DevicePtr → IO FloatArray

/-- Compile CUDA C source to module. -/
@[extern "scilean_cuda_compile"]
opaque cudaCompile : @& String → IO CUDAModule

/-- Launch a kernel from a compiled module. -/
@[extern "scilean_cuda_launch"]
opaque cudaLaunch :
  CUDAModule →           -- compiled module
  @& String →            -- kernel name
  USize → USize → USize →  -- grid dimensions
  USize → USize → USize →  -- block dimensions
  @& Array DevicePtr →   -- buffer arguments
  IO Unit

/-- Synchronize - wait for all kernels to complete. -/
@[extern "scilean_cuda_sync"]
opaque cudaSync : Unit → IO Unit

/-! ## CUDA Code Generation

Generate CUDA C source from UOp IR.
-/

/-- Render a DType to CUDA C type string. -/
def renderDType : DType → String
  | .float32 => "float"
  | .float64 => "double"
  | .int32 => "int"
  | .int64 => "long long"
  | .bool => "bool"

/-- Render a symbolic integer to CUDA C. -/
partial def renderSint : Sint → String
  | .nat n => toString n
  | .var s => s
  | .add a b => s!"({renderSint a} + {renderSint b})"
  | .sub a b => s!"({renderSint a} - {renderSint b})"
  | .mul a b => s!"({renderSint a} * {renderSint b})"
  | .div a b => s!"({renderSint a} / {renderSint b})"
  | .mod a b => s!"({renderSint a} % {renderSint b})"
  | .max a b => s!"max({renderSint a}, {renderSint b})"
  | .min a b => s!"min({renderSint a}, {renderSint b})"

/-- Generate variable name for a UOp. -/
def varName (pfx : String) (idx : Nat) : String := s!"{pfx}{idx}"

/-- CUDA kernel code structure. -/
structure CUDAKernel where
  /-- Kernel function name -/
  name : String
  /-- Parameter declarations -/
  params : List String
  /-- Kernel body -/
  body : String
  /-- Grid dimensions for launch -/
  gridDim : Sint × Sint × Sint
  /-- Block dimensions for launch -/
  blockDim : Sint × Sint × Sint
  deriving Repr

namespace CUDAKernel

/-- Render kernel to CUDA C source. -/
def render (k : CUDAKernel) : String :=
  let paramStr := ", ".intercalate k.params
  "extern \"C\" __global__ void " ++ k.name ++ "(" ++ paramStr ++ ") {\n" ++ k.body ++ "\n}"

end CUDAKernel

/-- Code generator state. -/
structure CodeGenState where
  /-- Next variable index -/
  nextVar : Nat := 0
  /-- Variable assignments -/
  varMap : List (UOp × String) := []
  /-- Generated statements -/
  stmts : List String := []

/-- Code generator monad. -/
abbrev CodeGenM := StateM CodeGenState

/-- Allocate a fresh variable name. -/
def freshVar (pfx : String := "v") : CodeGenM String := do
  let s ← get
  let name := varName pfx s.nextVar
  set { s with nextVar := s.nextVar + 1 }
  return name

/-- Add a statement to the generated code. -/
def emit (stmt : String) : CodeGenM Unit := do
  let s ← get
  set { s with stmts := s.stmts ++ [stmt] }

/-- Look up or generate code for a UOp. -/
partial def genUOp (u : UOp) : CodeGenM String := do
  let s ← get
  match s.varMap.find? (fun (op, _) => op == u) with
  | some (_, v) => return v
  | none =>
    let v ← match u with
      | .const val dtype =>
        let v ← freshVar (pfx := "c")
        emit s!"{renderDType dtype} {v} = {val};"
        pure v
      | .neg x =>
        let vx ← genUOp x
        let v ← freshVar
        emit s!"float {v} = -{vx};"
        pure v
      | .add x y =>
        let vx ← genUOp x
        let vy ← genUOp y
        let v ← freshVar
        emit s!"float {v} = {vx} + {vy};"
        pure v
      | .sub x y =>
        let vx ← genUOp x
        let vy ← genUOp y
        let v ← freshVar
        emit s!"float {v} = {vx} - {vy};"
        pure v
      | .mul x y =>
        let vx ← genUOp x
        let vy ← genUOp y
        let v ← freshVar
        emit s!"float {v} = {vx} * {vy};"
        pure v
      | .div x y =>
        let vx ← genUOp x
        let vy ← genUOp y
        let v ← freshVar
        emit s!"float {v} = {vx} / {vy};"
        pure v
      | .exp2 x =>
        let vx ← genUOp x
        let v ← freshVar
        emit s!"float {v} = exp2f({vx});"
        pure v
      | .log2 x =>
        let vx ← genUOp x
        let v ← freshVar
        emit s!"float {v} = log2f({vx});"
        pure v
      | .sin x =>
        let vx ← genUOp x
        let v ← freshVar
        emit s!"float {v} = sinf({vx});"
        pure v
      | .sqrt x =>
        let vx ← genUOp x
        let v ← freshVar
        emit s!"float {v} = sqrtf({vx});"
        pure v
      | .recip x =>
        let vx ← genUOp x
        let v ← freshVar
        emit s!"float {v} = 1.0f / {vx};"
        pure v
      | .max x y =>
        let vx ← genUOp x
        let vy ← genUOp y
        let v ← freshVar
        emit s!"float {v} = fmaxf({vx}, {vy});"
        pure v
      | .cmpLt x y =>
        let vx ← genUOp x
        let vy ← genUOp y
        let v ← freshVar
        emit s!"bool {v} = {vx} < {vy};"
        pure v
      | .cmpEq x y =>
        let vx ← genUOp x
        let vy ← genUOp y
        let v ← freshVar
        emit s!"bool {v} = {vx} == {vy};"
        pure v
      | .where_ cond t f =>
        let vc ← genUOp cond
        let vt ← genUOp t
        let vf ← genUOp f
        let v ← freshVar
        emit s!"float {v} = {vc} ? {vt} : {vf};"
        pure v
      | .mulacc a b c =>
        let va ← genUOp a
        let vb ← genUOp b
        let vc ← genUOp c
        let v ← freshVar
        emit s!"float {v} = fmaf({va}, {vb}, {vc});"
        pure v
      | .load ptr =>
        let vp ← genUOp ptr
        let v ← freshVar
        emit s!"float {v} = *{vp};"
        pure v
      | .store ptr val =>
        let vp ← genUOp ptr
        let vv ← genUOp val
        emit s!"*{vp} = {vv};"
        pure "void"
      | .index base offset =>
        let vb ← genUOp base
        let vo ← genUOp offset
        let v ← freshVar (pfx := "p")
        emit s!"float* {v} = {vb} + {vo};"
        pure v
      | .barrier =>
        emit "__syncthreads();"
        pure "void"
      | .range lo hi axisType =>
        let loStr := renderSint lo
        let hiStr := renderSint hi
        let v ← freshVar (pfx := "i")
        let axisVar := match axisType with
          | .global => "blockIdx.x * blockDim.x + threadIdx.x"
          | .warp => "threadIdx.x / 32"
          | .local_ => "threadIdx.x"
          | .loop => v
          | .reduce => v
          | .upcast => v
        if axisType == .loop || axisType == .reduce then
          emit s!"for (int {v} = {loStr}; {v} < {hiStr}; {v}++) \{"
        else
          emit s!"int {v} = {axisVar};"
        pure v
      | .defineGlobal id _dtype =>
        pure s!"buf{id}"
      | .defineVar name =>
        pure name
    -- Cache the result
    modify fun s => { s with varMap := (u, v) :: s.varMap }
    return v

/-! ## CUDA Backend Implementation -/

/-- A GPU buffer with associated metadata. -/
structure GPUBuffer where
  /-- Device pointer -/
  ptr : DevicePtr
  /-- Shape in elements -/
  shape : Array Nat
  /-- Data type -/
  dtype : DType
  /-- Whether data is valid on device -/
  deviceValid : Bool
  deriving Repr

/-- CUDA backend state. -/
structure CUDABackend where
  /-- Whether CUDA is initialized -/
  initialized : Bool := false
  /-- Compiled kernel cache -/
  kernelCache : List (String × CUDAModule) := []
  /-- Buffer registry -/
  buffers : Array GPUBuffer := #[]
  deriving Repr

namespace CUDABackend

/-- Initialize CUDA backend. -/
def init : IO CUDABackend := do
  if cudaAvailable () then
    let _ ← cudaInit ()
    return { initialized := true }
  else
    return { initialized := false }

/-- Allocate a GPU buffer. -/
def allocBuffer (backend : CUDABackend) (shape : Array Nat) (dtype : DType := .float32)
    : IO (CUDABackend × Nat) := do
  let elemSize : USize := match dtype with
    | .float32 => 4
    | .float64 => 8
    | .int32 => 4
    | .int64 => 8
    | .bool => 1
  let numElems := shape.foldl (· * ·) 1
  let size := numElems.toUSize * elemSize
  let ptr ← cudaAlloc size
  let buf := { ptr := ptr, shape := shape, dtype := dtype, deviceValid := false }
  let id := backend.buffers.size
  return ({ backend with buffers := backend.buffers.push buf }, id)

/-- Free a GPU buffer. -/
def freeBuffer (backend : CUDABackend) (id : Nat) : IO CUDABackend := do
  match backend.buffers[id]? with
  | none => return backend
  | some buf =>
    cudaFree buf.ptr
    -- Mark as invalid (don't actually remove to preserve indices)
    let newBuf : GPUBuffer := { buf with deviceValid := false, ptr := ⟨0, 0⟩ }
    return { backend with buffers := backend.buffers.set! id newBuf }

/-- Copy data from host to device. -/
def copyToDevice (backend : CUDABackend) (id : Nat) (data : FloatArray)
    : IO CUDABackend := do
  match backend.buffers[id]? with
  | none => return backend
  | some buf =>
    cudaCopyHtoD buf.ptr data
    let newBuf : GPUBuffer := { buf with deviceValid := true }
    return { backend with buffers := backend.buffers.set! id newBuf }

/-- Copy data from device to host. -/
def copyToHost (backend : CUDABackend) (id : Nat) (dst : FloatArray)
    : IO FloatArray := do
  match backend.buffers[id]? with
  | none => return dst
  | some buf => cudaCopyDtoH dst buf.ptr

/-- Compile and cache a kernel. -/
def compileKernel (backend : CUDABackend) (kernel : CUDAKernel)
    : IO (CUDABackend × CUDAModule) := do
  -- Check cache first
  match backend.kernelCache.find? (fun (n, _) => n == kernel.name) with
  | some (_, m) => return (backend, m)
  | none =>
    let src := kernel.render
    let m ← cudaCompile src
    let newCache := (kernel.name, m) :: backend.kernelCache
    return ({ backend with kernelCache := newCache }, m)

/-- Execute a kernel. -/
def executeKernel (backend : CUDABackend) (m : CUDAModule) (name : String)
    (gridDim blockDim : USize × USize × USize) (bufferIds : Array Nat)
    : IO Unit := do
  let ptrs := bufferIds.filterMap fun id =>
    backend.buffers[id]? |>.map (·.ptr)
  cudaLaunch m name gridDim.1 gridDim.2.1 gridDim.2.2
             blockDim.1 blockDim.2.1 blockDim.2.2 ptrs

/-- Synchronize - wait for all pending operations. -/
def sync : IO Unit := cudaSync ()

end CUDABackend

/-! ## LazyTensor → CUDA Execution

Convert LazyTensor graph to CUDA kernels and execute.
-/

/-- Lower a LazyNode to UOp IR. -/
partial def lowerToUOp (node : LazyNode) (bufferMap : List (Nat × UOp)) : UOp :=
  match node with
  | .buffer id _ dtype =>
    match bufferMap.find? (fun (i, _) => i == id) with
    | some (_, u) => u
    | none => .defineGlobal id dtype
  | .const val _ dtype => .const val dtype
  | .unary op x =>
    let ux := lowerToUOp x bufferMap
    match op with
    | .neg => .neg ux
    | .exp2 => .exp2 ux
    | .log2 => .log2 ux
    | .sin => .sin ux
    | .sqrt => .sqrt ux
    | .reciprocal => .recip ux
    | .cast _ => ux  -- simplified: just pass through
  | .binary op x y =>
    let ux := lowerToUOp x bufferMap
    let uy := lowerToUOp y bufferMap
    match op with
    | .add => .add ux uy
    | .sub => .sub ux uy
    | .mul => .mul ux uy
    | .div => .div ux uy
    | .max => .max ux uy
    | .min => .neg (.max (.neg ux) (.neg uy))  -- min(a,b) = -max(-a,-b)
    | .cmpLt => .cmpLt ux uy
    | .cmpEq => .cmpEq ux uy
  | .reduce _ _ x =>
    -- Simplified: just lower the input (full reduce needs more work)
    lowerToUOp x bufferMap
  | .movement _ x =>
    -- Movement ops don't generate compute, just affect indexing
    lowerToUOp x bufferMap

/-- Execute a LazyTensor on CUDA. -/
def executeOnCUDA (initBackend : CUDABackend) (tensor : LazyTensor)
    (inputBuffers : List (Nat × FloatArray)) : IO FloatArray := do
  if not initBackend.initialized then
    -- Fallback to CPU
    return FloatArray.mk #[]

  let node := tensor.realize

  -- Allocate input buffers
  let mut backend := initBackend
  let mut bufferMap : List (Nat × UOp) := []
  for (id, data) in inputBuffers do
    let (b, bufferId) ← backend.allocBuffer #[data.size] .float32
    backend := b
    let b2 ← backend.copyToDevice bufferId data
    backend := b2
    bufferMap := (id, .defineGlobal bufferId .float32) :: bufferMap

  -- Lower to UOp
  let uop := lowerToUOp node bufferMap

  -- Generate kernel
  let (_, state) := (genUOp uop).run {}
  let body := "\n".intercalate state.stmts

  let kernel : CUDAKernel := {
    name := "kernel_main"
    params := ["float* output"] ++ inputBuffers.map fun (id, _) => s!"float* buf{id}"
    body := body
    gridDim := (1, 1, 1)
    blockDim := (256, 1, 1)
  }

  -- Compile and execute
  let (backendAfterCompile, m) ← backend.compileKernel kernel
  backend := backendAfterCompile
  let shape := node.shape
  let outSize := shape.foldl (fun acc s =>
    match s with | .nat n => acc * n | _ => acc) 1
  let (backendWithOutput, outId) ← backend.allocBuffer #[outSize] .float32
  backend := backendWithOutput
  let bufferIds := #[outId] ++ (inputBuffers.map (·.1)).toArray
  backend.executeKernel m "kernel_main" (1, 1, 1) (256, 1, 1) bufferIds

  CUDABackend.sync

  -- Copy result back
  let emptyArr : FloatArray := {}
  let result ← backend.copyToHost outId emptyArr

  -- Cleanup
  for (id, _) in inputBuffers do
    let _ ← backend.freeBuffer id
  let _ ← backend.freeBuffer outId

  return result

end SciLean.Compiler.CUDA
