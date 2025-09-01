-- import SciLean.Data.DataArray.VectorType
-- import SciLean.Data.DataArray.MatrixType
import SciLean.Data.DataArray.Float
import SciLean.Data.DataArray.Algebra
import SciLean.Data.Vector

open SciLean



example : HasRnEquiv (Float^[10]) (Idx 10 × Unit) Float := by infer_instance
example : HasRnEquiv (Float^[10]^[20]) (Idx 20 × Idx 10 × Unit) Float := by infer_instance
example : HasRnEquiv (Float^[10,20]) ((Idx 10 × Idx 20) × Unit) Float := by infer_instance
-- example : DataArrayEquiv (Float^[10]^[20]) (Idx 20) (Float^[10]) := by infer_instance
-- example : DataArrayEquiv (Float^[10,20]^[30]) (Idx 30 × Idx 10 × Idx 20) Float := by infer_instance

-- example : VectorType.Base (Float^[10]) (Idx 10) Float := by infer_instance
-- example : VectorType.Base (Float^[10,20]) (Idx 10 × Idx 20) Float := by infer_instance
-- example : VectorType.Dense (Float^[10,20]) := by infer_instance
-- example : VectorType.Base (Float^[10,20]^[30]) (Idx 30 × Idx 10 × Idx 20) Float := by infer_instance
-- example : VectorType.Dense (Float^[10,20]^[30]) := by infer_instance

variable {R} [RealScalar R] [PlainDataType R] [BLAS (DataArray R) R R]

example : AddCommGroup (R^[10]) := by infer_instance
example : AddCommGroup (Float^[10]) := by infer_instance

-- example : MatrixType.Base (R^[2, 2]) (R^[2]) (R^[2]) := by infer_instance

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




example (i : Idx 10) (j : Idx 5) :
  (⊞ (_ : Idx 10) => ⊞ (_ : Idx 5) => 1.0)[i,j] = 1.0 := by simp only [simp_core]

example (ij : Idx 10×Idx 5) :
  (⊞ (_ : Idx 10) => ⊞ (_ : Idx 5) => 1.0)[ij] = 1.0 := by simp only [simp_core]



----------------------------------------------------------------------------------------------------
-- test index type inference -----------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

variable (x : Float^[4,5]^[2,3])

/-- info: fun ij => x[ij] : Idx 2 × Idx 3 → Float^[4, 5] -/
#guard_msgs in
#check fun ij => x[ij]

/-- info: fun i j => x[(i, j)] : Idx 2 → Idx 3 → Float^[4, 5] -/
#guard_msgs in
#check fun i j => x[i,j]

/-- info: fun ij kl => x[ij][kl] : Idx 2 × Idx 3 → Idx 4 × Idx 5 → Float -/
#guard_msgs in
#check fun ij kl => x[ij][kl]

/-- info: fun i j kl => x[(i, j)][kl] : Idx 2 → Idx 3 → Idx 4 × Idx 5 → Float -/
#guard_msgs in
#check fun i j kl => x[i,j][kl]

/-- info: fun ij k l => x[ij][(k, l)] : Idx 2 × Idx 3 → Idx 4 → Idx 5 → Float -/
#guard_msgs in
#check fun ij k l => x[ij][k,l]

/-- info: fun i j k l => x[(i, j)][(k, l)] : Idx 2 → Idx 3 → Idx 4 → Idx 5 → Float -/
#guard_msgs in
#check fun i j k l => x[i,j][k,l]

/-- info: fun ij k l => x[(ij, k, l)] : Idx 2 × Idx 3 → Idx 4 → Idx 5 → Float -/
#guard_msgs in
#check fun ij k l => x[ij,k,l]

/-- info: fun i j k l => x[((i, j), k, l)] : Idx 2 → Idx 3 → Idx 4 → Idx 5 → Float -/
#guard_msgs in
#check fun i j k l => x[(i,j),k,l]

-- "broken" as it clashes with `fun (i : Idx 2) (j : Idx 3) => x[i,j]`
/--
error: application type mismatch
  Prod.mk ij
argument
  ij
has type
  Idx 2 × Idx 3 : Type
but is expected to have type
  Idx 2 : Type
---
info: fun ij kl => x[(sorry, sorry)] : Idx 2 × Idx 3 → Idx 4 × Idx 5 → Float^[4, 5]
-/
#guard_msgs in
#check fun (ij : Idx 2 × Idx 3) (kl : Idx 4 × Idx 5) => x[ij,kl]

-- not using index notation works
/-- info: fun ij kl => x[(ij, kl)] : Idx 2 × Idx 3 → Idx 4 × Idx 5 → Float -/
#guard_msgs in
#check fun (ij : Idx 2 × Idx 3) (kl : Idx 4 × Idx 5) => getElem x (ij,kl) .intro
