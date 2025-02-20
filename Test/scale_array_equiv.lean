import SciLean.Data.DataArray.ScalarArrayEquiv
import SciLean.Data.VectorType.Base

open SciLean

example : ScalarArray Float FloatArray := by infer_instance
example : ScalarArrayEquiv (Float^[10]) FloatArray (Fin 10) Float Float := by infer_instance

example : ScalarArrayEquiv (Float^[10]) FloatArray (Fin 10) Float Float := by infer_instance
example : ScalarArrayEquiv (Float^[10]) FloatArray (Fin 10) Float Float := by infer_instance
example : ScalarArrayEquiv (Float^[10]^[20]) FloatArray (Fin 20 × Fin 10) Float Float := by infer_instance
example : ScalarArrayEquiv (Float^[10,20]) FloatArray (Fin 10 × Fin 20) Float Float := by infer_instance
example : ScalarArrayEquiv (Float^[10,20]^[30]) FloatArray (Fin 30 × Fin 10 × Fin 20) Float Float := by infer_instance

example : VectorType.Base (Float^[10]) (Fin 10) Float := by infer_instance
example : VectorType.Base (Float^[10,20]) (Fin 10 × Fin 20) Float := by infer_instance
example : VectorType.Dense (Float^[10,20]) := by infer_instance
example : VectorType.Base (Float^[10,20]^[30]) (Fin 30 × Fin 10 × Fin 20) Float := by infer_instance
example : VectorType.Dense (Float^[10,20]^[30]) := by infer_instance

variable {R} [RealScalar R] [PlainDataType R] {Array} [ScalarArray R Array]

example : AddCommGroup (R^[10]) := by infer_instance
example : AddCommGroup (Float^[10]) := by infer_instance

example : MatrixType.Base (R^[2, 2]) (R^[2]) (R^[2]) := by infer_instance


/-- info: ⊞[211.000000, 423.000000] -/
#guard_msgs in
#eval MatrixType.gemv 1.0 1.0 ⊞[1.0,2;3,4] ⊞[1.0,100.0] ⊞[10.0,20.0]

/-- info: ⊞[201.000000, 403.000000] -/
#guard_msgs in
#eval ⊞[1.0,2;3,4] * ⊞[1.0,100.0]

/-- info: ⊞[2.000000, 4.000000, 6.000000, 8.000000] -/
#guard_msgs in
#eval ⊞[1.0,2;3,4] + ⊞[1.0,2;3,4]
