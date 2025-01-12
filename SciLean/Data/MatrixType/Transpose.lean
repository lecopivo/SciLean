import SciLean.Data.MatrixType.Base

namespace SciLean

open Matrix MatrixType VectorType

class MatrixType.Transpose
      (M : Type*) (M' : outParam (Type*))
      {m n : outParam (Type*)} {_ : outParam (IndexType m)} {_ : outParam (IndexType n)}
      {R K : outParam (Type*)} {_ : outParam (RealScalar R)} {_ : outParam (Scalar R K)}
      (X Y : outParam (Type*)) [VectorType.Base X n K] [VectorType.Base Y m K]
      [MatrixType.Base M X Y] [MatrixType.Base M' Y X]
  where

    transpose (A : M) : M'
    transpose_spec (A : M) :
      toMatrix (transpose A)
      =
      let A := toMatrix A
      Aᵀ

    conjTranspose (A : M) : M'
    conjTranspose_spec (A : M) :
      toMatrix (conjTranspose A)
      =
      let A := toMatrix A
      Aᴴ


namespace DenseMatrixType

export MatrixType.Transpose (
  transpose
  transpose_spec
  conjTranspose
  conjTranspose_spec)

attribute [matrix_to_spec, matrix_from_spec ←]
  transpose_spec
  conjTranspose_spec


section Instances

variable
  {M : Type*}
  {n : Type*} {_ : IndexType n}
  {R K : Type*} {_ : RealScalar R} {_ : Scalar R K}
  {X : Type*} [VectorType.Base X n K]
  [MatrixType.Base M X X]
  [MatrixType.Transpose M M X X]

instance (priority:=low) : Star M := ⟨conjTranspose⟩

@[matrix_to_spec, matrix_from_spec ←]
theorem star_spec (A : M) :
    toMatrix (star A) = star (toMatrix A) := by
  conv => lhs; dsimp[star]
  simp only [conjTranspose_spec]
  rfl


end Instances


end DenseMatrixType

end SciLean
