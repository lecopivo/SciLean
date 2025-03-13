-- import SciLean.Data.MatrixType.MatMul
-- import SciLean.Data.MatrixType.Transpose
-- import SciLean.Data.MatrixType.Square
-- import SciLean.Data.ArrayType
-- import SciLean.Data.DataArray
-- import SciLean.Data.StructType
-- import SciLean.Analysis.Scalar
import SciLean

open SciLean

/-!  This file test that `MatrixType` and `VectorType` instances do not break normal instances
-/

example {K : Type} [RCLike K] {X : Type} [SemiHilbert K X] : HSMul K X X := by infer_instance

example {R : Type _} [RealScalar R] {X : Type _}
  [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X] :
  Inner R X := by infer_instance

example   {R : Type _} [RealScalar R]
  {X : Type _} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X] :
  HAdd X X X := by infer_instance

example : Inner Float (Float^[2]) := by infer_instance

open VectorType in
example {R} [RealScalar R] {n nn} [IdxType n nn] {X} [VectorType.Base X n R] [InjectiveGetElem X n] :
   (instAdjointSpace : AdjointSpace R X) = (instAdjointSpaceReal : AdjointSpace R X) := by
  rfl

example {K : Type} [RealScalar K]
  {Y : Type} [NormedAddCommGroup Y] [Module K Y] : ZeroStruct (Y × Y) Unit fun _ => Y × Y := by
  infer_instance
