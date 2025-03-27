import SciLean.Data.DataArray.TensorProduct
import SciLean.Data.DataArray.DataArrayEquiv
import SciLean.Algebra.TensorProduct.Prod
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
#eval (vecMatMulAdd (X:=Float^[2]) (YX:=Float^[3,2]) (1.0 : Float) ⊞[0.1,1.0,10.0] (⊞[1.0,2.0,3.0] ⊗ ⊞[100.0,1000.0]) 0 0)


/--
info: (⊞[1.0, 2.0], ⊞[10.0, 100.0]) ⊗ ⊞[0.1, 1e-2] : ProdMatrixCol (Float^[2, 2]) (Float^[2, 2])
-/
#guard_msgs in
#check (⊞[1.0,2.0],⊞[10.0,100.0]) ⊗ ⊞[0.1,0.01]


/--
info: ⊞[0.1, 1e-2] ⊗ (⊞[1.0, 2.0], ⊞[10.0, 100.0]) : ProdMatrixRow (Float^[2, 2]) (Float^[2, 2])
-/
#guard_msgs in
#check ⊞[0.1,0.01] ⊗ (⊞[1.0,2.0],⊞[10.0,100.0])


set_option synthInstance.maxSize 5000

/--
info: ProdMatrixCol (ProdMatrixRow (Float^[2, 2]) (Float^[2, 2])) (ProdMatrixRow (Float^[2, 2]) (Float^[2, 2])) : Type
-/
#guard_msgs in
#check (Float^[2] × Float^[2]) ⊗ (Float^[2] × Float^[2])


/--
info: (⊞[1.0, 2.0], ⊞[10.0, 100.0], ⊞[0.1, 1e-2]) ⊗
  (⊞[1.0, 2.0], ⊞[10.0, 100.0],
    ⊞[0.1,
        1e-2]) : ProdMatrixCol (ProdMatrixRow (Float^[2, 2]) (ProdMatrixRow (Float^[2, 2]) (Float^[2, 2])))
  (ProdMatrixCol (ProdMatrixRow (Float^[2, 2]) (ProdMatrixRow (Float^[2, 2]) (Float^[2, 2])))
    (ProdMatrixRow (Float^[2, 2]) (ProdMatrixRow (Float^[2, 2]) (Float^[2, 2]))))
-/
#guard_msgs in
#check (⊞[1.0,2.0],⊞[10.0,100.0],⊞[0.1,0.01]) ⊗ (⊞[1.0,2.0],⊞[10.0,100.0],⊞[0.1,0.01])


/--
info: inferInstance : TensorProductType Float (Float^[2] × Float^[2]) (Float^[2] × Float^[2])
  (ProdMatrixCol (ProdMatrixRow (Float^[2, 2]) (Float^[2, 2])) (ProdMatrixRow (Float^[2, 2]) (Float^[2, 2])))
-/
#guard_msgs in
#check (by infer_instance : TensorProductType Float (Float^[2] × Float^[2]) (Float^[2] × Float^[2]) _)
