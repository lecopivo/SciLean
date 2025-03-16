import SciLean.Data.DataArray.TensorProduct
import SciLean.Data.DataArray.DataArrayEquiv
-- import SciLean.Data.DataArray.VectorType
-- import SciLean.Data.DataArray.MatrixType
import SciLean.Data.DataArray.Float

open SciLean

set_default_scalar Float


/-- info: ⊞[100.000000, 1000.000000, 200.000000, 2000.000000, 300.000000, 3000.000000] -/
#guard_msgs in
#eval (⊞[1.0,2.0,3.0] ⊗ ⊞[100.0,1000.0])


/-- info: ⊞[100.000000, 200.000000, 300.000000, 1000.000000, 2000.000000, 3000.000000] -/
#guard_msgs in
#eval (⊞[100.0,1000.0] ⊗ ⊞[1.0,2.0,3.0])

/-- info: ⊞[1020.000000, 2040.000000, 3060.000000] -/
#guard_msgs in
#eval (⊞[1.0,2.0,3.0] ⊗ ⊞[100.0,1000.0]) * ⊞[0.2,1.0]


/-- info: ⊞[3210.000000, 32100.000000] -/
#guard_msgs in
#eval (⊞[100.0,1000.0] ⊗ ⊞[1.0,2.0,3.0]) * ⊞[0.1,1.0,10.]


open TensorProductType in
/-- info: ⊞[3210.000000, 32100.000000] -/
#guard_msgs in
#eval (matHVecMul (X:=Float^[2]) (YX:=Float^[3,2]) (1.0 : Float) (⊞[1.0,2.0,3.0] ⊗ ⊞[100.0,1000.0]) ⊞[0.1,1.0,10.0] 0 0)
