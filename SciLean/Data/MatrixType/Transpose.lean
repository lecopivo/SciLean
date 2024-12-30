import SciLean.Data.MatrixType.Base

namespace SciLean

open Matrix

class DenseMatrixType.Transpose
      (M : Type*) (M' : outParam (Type*))
      {m n : outParam (Type*)} [IndexType m] [IndexType n]
      {R K : outParam (Type*)} [RealScalar R] [Scalar R K]
      (X Y : outParam (Type*)) [VectorType.Base X n K] [VectorType.Base Y m K]
      [DenseMatrixType.Base M X Y] [DenseMatrixType.Base M' Y X]
  where

    transpose (A : M) : M'
    transpose_spec (A : M) :
      mequiv (transpose A)
      =
      let A := mequiv A
      Aᵀ

    conjTranspose (A : M) : M'
    conjTranspose_spec (A : M) :
      mequiv (conjTranspose A)
      =
      let A := mequiv A
      Aᴴ


namespace DenseMatrixType

export DenseMatrixType.Transpose (
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
  {n : Type*} [IndexType n]
  {R K : Type*} [RealScalar R] [Scalar R K]
  {X : Type*} [VectorType.Base X n K]
  [DenseMatrixType.Base M X X]
  [DenseMatrixType.Transpose M M X X]

instance : Star M := ⟨conjTranspose⟩

@[matrix_to_spec, matrix_from_spec ←]
theorem star_spec (A : M) :
    mequiv (star A) = star (mequiv A) := by
  conv => lhs; dsimp[star]
  simp only [conjTranspose_spec]
  rfl


end Instances


end DenseMatrixType

end SciLean
