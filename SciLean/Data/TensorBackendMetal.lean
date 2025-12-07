/-
Metal Backend for TensorBackend Typeclass

Provides GPU-accelerated tensor operations via Apple Metal.
Falls back to CPU when Metal is not available.

Key design:
- Uses ByteArray (Float32) as native Metal buffer type
- CPU fallback for small arrays (n ≤ 4096) via vDSP
- GPU dispatch for large arrays
- Zero-copy FFI where possible
-/
import SciLean.Data.TensorBackend
import SciLean.FFI.Metal
import SciLean.FFI.Float32Array
import SciLean.Data.DataArray.TensorOperations

namespace SciLean

/-! ## Metal Buffer Type -/

/-- Metal-compatible buffer wrapping ByteArray with Float32 data.
    This is the native storage format for Metal operations. -/
structure MetalBuffer where
  /-- Raw byte data containing Float32 values -/
  data : ByteArray
  /-- Number of Float32 elements (data.size / 4) -/
  size : Nat
  /-- Invariant: data.size = size * 4 -/
  size_valid : data.size = size * 4 := by sorry_proof

namespace MetalBuffer

/-- Create an empty buffer -/
def empty : MetalBuffer := ⟨ByteArray.empty, 0, rfl⟩

/-- Create a buffer filled with a constant value -/
def fill (n : Nat) (v : Float32) : MetalBuffer :=
  ⟨Metal.Float32.fill n.toUSize v, n, sorry_proof⟩

/-- Create a zero-initialized buffer -/
def zeros (n : Nat) : MetalBuffer := fill n 0.0

/-- Get element at index (bounds unchecked) -/
def uget (buf : MetalBuffer) (i : USize) : Float32 :=
  buf.data.ugetFloat32 (i * 4)

/-- Set element at index (returns new buffer) -/
def uset (buf : MetalBuffer) (i : USize) (v : Float32) : MetalBuffer :=
  ⟨buf.data.usetFloat32 (i * 4) v, buf.size, sorry_proof⟩

end MetalBuffer

/-! ## TensorBackend Instance for Metal -/

/-- Metal GPU backend using Float32 ByteArray storage.
    Automatically falls back to CPU for small arrays. -/
instance : TensorBackend MetalBuffer where
  device := .metal

  zeros n := MetalBuffer.zeros n

  copy src := src  -- MetalBuffer is immutable

  add x y :=
    ⟨Metal.Float32.add x.size.toUSize x.data y.data, x.size, sorry_proof⟩

  scal a x := Id.run do
    -- Scale by multiplying with broadcast scalar
    let aArr := Metal.Float32.fill x.size.toUSize a.toFloat32
    ⟨Metal.Float32.mul x.size.toUSize aArr x.data, x.size, sorry_proof⟩

  adds x a := Id.run do
    let aArr := Metal.Float32.fill x.size.toUSize a.toFloat32
    ⟨Metal.Float32.add x.size.toUSize x.data aArr, x.size, sorry_proof⟩

  mul x y :=
    ⟨Metal.Float32.mul x.size.toUSize x.data y.data, x.size, sorry_proof⟩

  dot x y := Id.run do
    let prod := Metal.Float32.mul x.size.toUSize x.data y.data
    (Metal.Float32.reduceSum x.size.toUSize prod).toFloat

  sum x := (Metal.Float32.reduceSum x.size.toUSize x.data).toFloat

  max x := (Metal.Float32.reduceMax x.size.toUSize x.data).toFloat

  gemv m n A x :=
    -- For now, implement via GEMM with n=1
    -- TODO: Add dedicated Metal GEMV kernel
    let xCol := x.data  -- Treat as m×1 matrix
    let result := Metal.Float32.gemmAuto m.toUSize n.toUSize 1 A.data xCol
    ⟨result, m, sorry_proof⟩

  gemm m k n A B :=
    ⟨Metal.Float32.gemmAuto m.toUSize k.toUSize n.toUSize A.data B.data, m * n, sorry_proof⟩

  gemmScaled m k n alpha A B beta C := Id.run do
    -- C = alpha * A * B + beta * C
    let AB := Metal.Float32.gemmAuto m.toUSize k.toUSize n.toUSize A.data B.data
    let alphaArr := Metal.Float32.fill (m * n).toUSize alpha.toFloat32
    let betaArr := Metal.Float32.fill (m * n).toUSize beta.toFloat32
    let alphaAB := Metal.Float32.mul (m * n).toUSize alphaArr AB
    let betaC := Metal.Float32.mul (m * n).toUSize betaArr C.data
    ⟨Metal.Float32.add (m * n).toUSize alphaAB betaC, m * n, sorry_proof⟩

  exp x :=
    ⟨Metal.Float32.exp2 x.size.toUSize x.data, x.size, sorry_proof⟩

  log x :=
    ⟨Metal.Float32.log2 x.size.toUSize x.data, x.size, sorry_proof⟩

  softmax x :=
    ⟨Metal.Float32.softmax x.size.toUSize x.data, x.size, sorry_proof⟩

/-! ## Float64 ↔ Float32 Conversion Helpers -/

/-- Convert FloatArray (Float64) to MetalBuffer (Float32) -/
def floatArrayToMetalBuffer (arr : FloatArray) : MetalBuffer := Id.run do
  let mut bytes := ByteArray.emptyWithCapacity (arr.size * 4)
  -- Pre-allocate
  for _ in [0:arr.size * 4] do
    bytes := bytes.push 0
  -- Fill with Float32 values
  for i in [0:arr.size] do
    let f64 := arr.uget i.toUSize sorry_proof
    let f32 : Float32 := f64.toFloat32
    bytes := bytes.usetFloat32 (i * 4).toUSize f32
  ⟨bytes, arr.size, sorry_proof⟩

/-- Convert MetalBuffer (Float32) to FloatArray (Float64) -/
def MetalBuffer.toFloatArray (buf : MetalBuffer) : FloatArray := Id.run do
  let mut arr : FloatArray := .emptyWithCapacity buf.size
  for i in [0:buf.size] do
    let f32 := buf.uget i.toUSize
    arr := arr.push f32.toFloat
  arr

/-! ## Smart Backend Selection -/

/-- Use Metal GEMM when available, with automatic kernel selection.
    Falls back to CPU for unavailable Metal or very small matrices. -/
def gemmWithMetal (m k n : Nat) (A B : FloatArray) : FloatArray :=
  if Metal.isAvailable () && m * n >= 64 then
    -- Convert to Float32, run on GPU, convert back
    let aBuf := floatArrayToMetalBuffer A
    let bBuf := floatArrayToMetalBuffer B
    let cBuf : MetalBuffer := ⟨Metal.Float32.gemmAuto m.toUSize k.toUSize n.toUSize aBuf.data bBuf.data, m * n, sorry_proof⟩
    cBuf.toFloatArray
  else
    TensorBackend.gemm m k n A B

/-- Use Metal GEMV when available -/
def gemvWithMetal (m n : Nat) (A x : FloatArray) : FloatArray :=
  if Metal.isAvailable () && m >= 64 then
    let aBuf := floatArrayToMetalBuffer A
    let xBuf := floatArrayToMetalBuffer x
    -- Use GEMM with n=1 column
    let yBuf : MetalBuffer := ⟨Metal.Float32.gemmAuto m.toUSize n.toUSize 1 aBuf.data xBuf.data, m, sorry_proof⟩
    yBuf.toFloatArray
  else
    TensorBackend.gemv m n A x

/-- Use Metal add when available -/
def addWithMetal (x y : FloatArray) : FloatArray :=
  if Metal.isAvailable () && x.size >= 4096 then
    let xBuf := floatArrayToMetalBuffer x
    let yBuf := floatArrayToMetalBuffer y
    let zBuf : MetalBuffer := ⟨Metal.Float32.add x.size.toUSize xBuf.data yBuf.data, x.size, sorry_proof⟩
    zBuf.toFloatArray
  else
    TensorBackend.add x y

/-- Use Metal softmax when available -/
def softmaxWithMetal (x : FloatArray) : FloatArray :=
  if Metal.isAvailable () && x.size >= 256 then
    let xBuf := floatArrayToMetalBuffer x
    let yBuf : MetalBuffer := ⟨Metal.Float32.softmax x.size.toUSize xBuf.data, x.size, sorry_proof⟩
    yBuf.toFloatArray
  else
    TensorBackend.softmax x

/-! ## DataArrayN Wiring -/

/-- Matrix multiply using Metal when available
    Wraps DataArrayN operations with Metal backend -/
def contractMiddleAddRWithMetal
    {I : Type} {nI} [IndexType I nI] [Fold I]
    {J : Type} {nJ} [IndexType J nJ] [Fold J]
    {K : Type} {nK} [IndexType K nK] [Fold K]
    (a : Float) (x : Float^[I,J]) (y : Float^[J,K]) (b : Float) (z : Float^[I,K]) : Float^[I,K] :=
  if Metal.isAvailable () && a == 1.0 && b == 0.0 && nI * nK >= 64 then
    -- Use Metal GEMM directly (bypassing BLAS)
    let xArr := DataArrayN.toFloatArray x
    let yArr := DataArrayN.toFloatArray y
    let result := gemmWithMetal nI nJ nK xArr yArr
    DataArrayN.fromFloatArray result
  else if a == 1.0 && b == 0.0 then
    -- Use BLAS for CPU
    let xArr := DataArrayN.toFloatArray x
    let yArr := DataArrayN.toFloatArray y
    let result := TensorBackend.gemm nI nJ nK xArr yArr
    DataArrayN.fromFloatArray result
  else
    -- Fall back to naive implementation for general α, β
    DataArrayN.contractMiddleAddRNaive a x y b z

/-- Matrix-vector multiply using Metal when available -/
def contractRightAddRWithMetal
    {I : Type} {nI} [IndexType I nI] [Fold I]
    {J : Type} {nJ} [IndexType J nJ] [Fold J]
    (a : Float) (x : Float^[I,J]) (y : Float^[J]) (b : Float) (z : Float^[I]) : Float^[I] :=
  if Metal.isAvailable () && a == 1.0 && b == 0.0 && nI >= 64 then
    -- Use Metal GEMV
    let xArr := DataArrayN.toFloatArray x
    let yArr := DataArrayN.toFloatArray y
    let result := gemvWithMetal nI nJ xArr yArr
    DataArrayN.fromFloatArray result
  else
    -- Fall back to existing implementation
    DataArrayN.contractRightAddR a x y b z

/-! ## Float32 Native Operations (Zero-Copy) -/

/-- Native Float32 matrix multiply - no conversion overhead -/
def gemmFloat32 (m k n : Nat) (A B : ByteArray) : ByteArray :=
  Metal.Float32.gemmAuto m.toUSize k.toUSize n.toUSize A B

/-- Native Float32 softmax -/
def softmaxFloat32 (x : ByteArray) : ByteArray :=
  Metal.Float32.softmax (x.size / 4).toUSize x

/-- Native Float32 bias + ReLU -/
def biasReluFloat32 (n stride : Nat) (input bias : ByteArray) : ByteArray :=
  Metal.Float32.biasRelu n.toUSize stride.toUSize input bias

/-- Native Float32 layer normalization -/
def layerNormFloat32 (n hiddenSize : Nat) (input gamma beta : ByteArray) : ByteArray :=
  Metal.Float32.layerNorm n.toUSize hiddenSize.toUSize input gamma beta

/-- Native Float32 flash attention -/
def flashAttentionFloat32 (seqLen headDim : Nat) (Q K V : ByteArray) : ByteArray :=
  Metal.Float32.flashAttention seqLen.toUSize headDim.toUSize Q K V

/-- Native Float32 causal flash attention -/
def flashAttentionCausalFloat32 (seqLen headDim : Nat) (Q K V : ByteArray) : ByteArray :=
  Metal.Float32.flashAttentionCausal seqLen.toUSize headDim.toUSize Q K V

/-- Native Float32 batched softmax -/
def softmaxBatchedFloat32 (numRows rowSize : Nat) (x : ByteArray) : ByteArray :=
  Metal.Float32.softmaxBatched numRows.toUSize rowSize.toUSize x

/-! ## Attention Operations for DataArrayN -/

/-- Single-head attention using Metal GPU
    Q, K, V : Float^[seqLen, headDim]
    output  : Float^[seqLen, headDim]
    Computes: softmax(Q * K^T / sqrt(headDim)) * V
    Note: Requires Metal to be available, otherwise returns V unchanged -/
def attentionWithMetal
    {S : Type} {seqLen} [IndexType S seqLen]
    {D : Type} {headDim} [IndexType D headDim]
    (Q K V : Float^[S, D]) : Float^[S, D] :=
  if Metal.isAvailable () then
    let qArr := Q.data.byteData
    let kArr := K.data.byteData
    let vArr := V.data.byteData
    let result := flashAttentionFloat32 seqLen headDim qArr kArr vArr
    ⟨⟨result, sorry_proof⟩, sorry_proof⟩
  else
    V  -- CPU fallback: identity (no attention applied)

/-- Causal (masked) attention using Metal GPU
    Only attends to positions ≤ current position
    Note: Requires Metal to be available, otherwise returns V unchanged -/
def attentionCausalWithMetal
    {S : Type} {seqLen} [IndexType S seqLen]
    {D : Type} {headDim} [IndexType D headDim]
    (Q K V : Float^[S, D]) : Float^[S, D] :=
  if Metal.isAvailable () then
    let qArr := Q.data.byteData
    let kArr := K.data.byteData
    let vArr := V.data.byteData
    let result := flashAttentionCausalFloat32 seqLen headDim qArr kArr vArr
    ⟨⟨result, sorry_proof⟩, sorry_proof⟩
  else
    V  -- CPU fallback: identity (no attention applied)

/-- Row-wise softmax using Metal when available
    x : Float^[rows, cols]
    output: softmax applied to each row independently -/
def softmaxRowsWithMetal
    {R : Type} {nRows} [IndexType R nRows] [Fold R]
    {C : Type} {nCols} [IndexType C nCols] [Fold C]
    (x : Float^[R, C]) : Float^[R, C] :=
  if Metal.isAvailable () && nRows * nCols >= 256 then
    let xArr := x.data.byteData
    let result := softmaxBatchedFloat32 nRows nCols xArr
    ⟨⟨result, sorry_proof⟩, sorry_proof⟩
  else
    -- CPU fallback using existing softmax from TensorOperations
    DataArrayN.softmax x

/-! ## Backend Selection Helper -/

/-- Check if Metal acceleration is available -/
def metalAvailable : Bool := Metal.isAvailable ()

/-- Print backend status -/
def printBackendStatus : IO Unit := do
  if metalAvailable then
    IO.println "Metal GPU acceleration: AVAILABLE"
    IO.println "  - Using MPS for large GEMM (≥512×512)"
    IO.println "  - Using Simd for medium GEMM (256-512)"
    IO.println "  - Using CPU/vDSP for small ops (≤4096 elements)"
  else
    IO.println "Metal GPU acceleration: NOT AVAILABLE (using CPU/BLAS)"

end SciLean
