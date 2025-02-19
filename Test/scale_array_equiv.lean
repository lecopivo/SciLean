import SciLean.Data.DataArray.ScalarArrayEquiv

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
example : VectorType.Base (Float^[10,20]^[30]) (Fin 30 × Fin 10 × Fin 20) Float := by infer_instance

variable {R} [RealScalar R] [PlainDataType R] {Array} [ScalarArray R Array]

example : Module R (R^[10]) := by infer_instance
example : MatrixType.Base (R^[2, 2]) (R^[2]) (R^[2]) := by infer_instance


/-- info: ⊞[211.000000, 423.000000] -/
#guard_msgs in
#eval MatrixType.gemv 1.0 1.0 ⊞[1.0,2;3,4] ⊞[1.0,100.0] ⊞[10.0,20.0]
