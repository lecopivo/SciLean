/-
Metal Backend for TensorBackend Typeclass

Provides GPU-accelerated tensor operations via Apple Metal.
Falls back to CPU when Metal is not available.
-/
import SciLean.Data.TensorBackend
import SciLean.FFI.Metal
import SciLean.Data.DataArray.TensorOperations

namespace SciLean

/-! ## Metal-Accelerated Operations -/

/-- Use Metal GEMM when available, otherwise fall back to CPU -/
def gemmWithMetal (m k n : Nat) (A B : FloatArray) : FloatArray :=
  if Metal.isAvailable () then
    Metal.gemm m.toUSize k.toUSize n.toUSize A B
  else
    TensorBackend.gemm m k n A B

/-- Use Metal GEMV when available, otherwise fall back to CPU -/
def gemvWithMetal (m n : Nat) (A x : FloatArray) : FloatArray :=
  if Metal.isAvailable () then
    Metal.gemv m.toUSize n.toUSize A x
  else
    TensorBackend.gemv m n A x

/-- Use Metal add when available, otherwise fall back to CPU -/
def addWithMetal (x y : FloatArray) : FloatArray :=
  if Metal.isAvailable () then
    Metal.add x.size.toUSize x y
  else
    TensorBackend.add x y

/-! ## DataArrayN Wiring -/

/-- Matrix multiply using Metal when available
    Wraps DataArrayN operations with Metal backend -/
def contractMiddleAddRWithMetal
    {I : Type} {nI} [IndexType I nI] [Fold I]
    {J : Type} {nJ} [IndexType J nJ] [Fold J]
    {K : Type} {nK} [IndexType K nK] [Fold K]
    (a : Float) (x : Float^[I,J]) (y : Float^[J,K]) (b : Float) (z : Float^[I,K]) : Float^[I,K] :=
  if Metal.isAvailable () && a == 1.0 && b == 0.0 then
    -- Use Metal GEMM directly
    let xArr := DataArrayN.toFloatArray x
    let yArr := DataArrayN.toFloatArray y
    let result := Metal.gemm nI.toUSize nJ.toUSize nK.toUSize xArr yArr
    DataArrayN.fromFloatArray result
  else
    -- Fall back to naive implementation
    DataArrayN.contractMiddleAddRNaive a x y b z

/-- Matrix-vector multiply using Metal when available -/
def contractRightAddRWithMetal
    {I : Type} {nI} [IndexType I nI] [Fold I]
    {J : Type} {nJ} [IndexType J nJ] [Fold J]
    (a : Float) (x : Float^[I,J]) (y : Float^[J]) (b : Float) (z : Float^[I]) : Float^[I] :=
  if Metal.isAvailable () && a == 1.0 && b == 0.0 then
    -- Use Metal GEMV
    let xArr := DataArrayN.toFloatArray x
    let yArr := DataArrayN.toFloatArray y
    let result := Metal.gemv nI.toUSize nJ.toUSize xArr yArr
    DataArrayN.fromFloatArray result
  else
    -- Fall back to existing implementation
    DataArrayN.contractRightAddR a x y b z

/-! ## Backend Selection Helper -/

/-- Check if Metal acceleration is available -/
def metalAvailable : Bool := Metal.isAvailable ()

/-- Print backend status -/
def printBackendStatus : IO Unit := do
  if metalAvailable then
    IO.println "Metal GPU acceleration: AVAILABLE"
  else
    IO.println "Metal GPU acceleration: NOT AVAILABLE (using CPU/BLAS)"

end SciLean
