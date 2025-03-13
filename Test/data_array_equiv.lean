import SciLean.Data.DataArray.VectorType
import SciLean.Data.DataArray.MatrixType
import SciLean.Data.DataArray.Float
import SciLean.Data.Vector

open SciLean

example : DataArrayEquiv (Float^[10]) (Idx 10) Float := by infer_instance
example : DataArrayEquiv (Float^[10]^[20]) (Idx 20 × Idx 10) Float := by infer_instance
example : DataArrayEquiv (Float^[10,20]) (Idx 10 × Idx 20) Float := by infer_instance
example : DataArrayEquiv (Float^[10]^[20]) (Idx 20) (Float^[10]) := by infer_instance
example : DataArrayEquiv (Float^[10,20]^[30]) (Idx 30 × Idx 10 × Idx 20) Float := by infer_instance

example : VectorType.Base (Float^[10]) (Idx 10) Float := by infer_instance
example : VectorType.Base (Float^[10,20]) (Idx 10 × Idx 20) Float := by infer_instance
example : VectorType.Dense (Float^[10,20]) := by infer_instance
example : VectorType.Base (Float^[10,20]^[30]) (Idx 30 × Idx 10 × Idx 20) Float := by infer_instance
example : VectorType.Dense (Float^[10,20]^[30]) := by infer_instance

variable {R} [RealScalar R] [PlainDataType R] [BLAS (DataArray R) R R] [LawfulBLAS (DataArray R) R R]

example : AddCommGroup (R^[10]) := by infer_instance
example : AddCommGroup (Float^[10]) := by infer_instance

example : MatrixType.Base (R^[2, 2]) (R^[2]) (R^[2]) := by infer_instance

example : GetElem' (Float^[n]^[m]) (Idx m×Idx n) Float := by infer_instance
example : IsAddGetElem (Float^[n]^[m]) (Idx m × Idx n) := by infer_instance
example : IsNegGetElem (Float^[n]^[m]) (Idx m × Idx n) := by infer_instance
example : IsModuleGetElem Float (Float^[n]^[m]) (Idx m × Idx n) := by infer_instance
example : IsInnerGetElem Float (Float^[n]^[m]) (Idx m × Idx n) := by infer_instance
example : IsContinuousGetElem (Float^[n]^[m]) (Idx m × Idx n) := by infer_instance

example : GetElem' (Float^[n]^[m]) (Idx m) (Float^[n]) := by infer_instance
example : IsAddGetElem (Float^[n]^[m]) (Idx m) := by infer_instance
example : IsNegGetElem (Float^[n]^[m]) (Idx m) := by infer_instance
example : IsModuleGetElem Float (Float^[n]^[m]) (Idx m) := by infer_instance
example : IsInnerGetElem Float (Float^[n]^[m]) (Idx m) := by infer_instance
-- this instance is currently short circuited by an instancence making `IsContinuousGetElem` true all the time
-- there are some strage interactions with `VectorType.Base` we could not resolve
example : IsContinuousGetElem (Float^[n]^[m]) (Idx m) := by infer_instance

example : GetElem' (Float^[k]^[n]^[m]) (Idx m) (Float^[k]^[n]) := by infer_instance
-- example : IsAddGetElem (Float^[k]^[n]^[m]) (Idx m) := by infer_instance
-- example : IsNegGetElem (Float^[k]^[n]^[m]) (Idx m) := by infer_instance
-- example : IsModuleGetElem Float (Float^[k]^[n]^[m]) (Idx m) := by infer_instance


example : GetElem' (Float^[k]^[n]^[m]) (Idx m×Idx n) (Float^[k]) := by infer_instance
-- example : IsModuleGetElem Float (Float^[k]^[n]^[m]) (Idx m×Idx n) := by infer_instance

example : GetElem' (Float^[k]^[n]^[m]) (Idx m×Idx n×Idx k) (Float) := by infer_instance
example : IsModuleGetElem Float (Float^[k]^[n]^[m]) (Idx m×Idx n×Idx k) := by infer_instance


/-- info: ⊞[1.0, 2, 3] : Float^[3] -/
#guard_msgs in
#check ⊞[1.0,2,3]

-- /-- info: ⊞[1.0, 2, 3] : Vector Float 3 -/
-- #guard_msgs in
-- #check (⊞[1.0,2,3] : Vector Float 3)

/-- info: ⊞[1.0, 2; 3, 4] : Float^[2, 2] -/
#guard_msgs in
#check ⊞[1.0,2;3,4]

/-- info: ⊞[211.000000, 423.000000] -/
#guard_msgs in
#eval MatrixType.gemv 1.0 1.0 ⊞[1.0,2;3,4] ⊞[1.0,100.0] ⊞[10.0,20.0]

/-- info: ⊞[201.000000, 403.000000] -/
#guard_msgs in
#eval ⊞[1.0,2;3,4] * ⊞[1.0,100.0]

/-- info: ⊞[2.000000, 4.000000, 6.000000, 8.000000] -/
#guard_msgs in
#eval ⊞[1.0,2;3,4] + ⊞[1.0,2;3,4]
