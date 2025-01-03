import SciLean

open SciLean


section missing
end missing


def test1 : IO Unit := do

  let v : FloatVector (Fin 3) := VectorType.fromVec ![1,2,3]
  let v' : FloatVector' (.subvector (offset := 3) (inc := 2)) (Fin 3) :=
    VectorType.fromVec ![1,2,3]

  let A : FloatMatrix' .RowMajor .normal (Fin 3) (Fin 3) := MatrixType.fromMatrix !![1,1,1; 0,-1,0; -1, 0, 42]

  IO.println v.data
  IO.println (10.0•v').data.data
  IO.println (v'+v').data.data

  IO.println (MatrixType.gemv 1 1 A v 0).data
  IO.println ""
  IO.println A.data
  IO.println ""
  IO.println (MatrixType.row A 0).data
  IO.println (MatrixType.col A 1).data
  IO.println (MatrixType.Square.diag A).data


def main : IO Unit := do
  test1
