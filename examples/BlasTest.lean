import LeanBLAS

open BLAS

#exit
def main : IO Unit := do

  let v := DenseVector.ofFn (Array:=FloatArray) (vstrg := .normal) (fun (i : Fin 3) => i.1.toFloat)

  IO.println s!"v := {v}"
  IO.println s!"0.1•v := {v.scal 0.1}"
  IO.println s!"v+v := {v.axpy 1 v}"
  IO.println s!"‖v‖₂² := {v.nrm2}"
