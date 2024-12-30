import SciLean.Data.MatrixType.Base

namespace SciLean

open Matrix
class DenseMatrixType.Square
      (M : Type*)
      {n : outParam (Type*)} [IndexType n]
      {R K : outParam (Type*)} [RealScalar R] [Scalar R K]
      (X : outParam (Type*)) [VectorType.Base X n K]
      [DenseMatrixType.Base M X X]
  where

  /-- Turn vector `x` into diagonal matrix -/
  diagonal (x : X) : M
  diagonal_spec (x : X) [DecidableEq n] :
    mequiv (diagonal x)
    =
    let x := VectorType.vequiv x
    Matrix.diagonal x

  /-- Extract diagonal of matrix -/
  diag (A : M) : X
  diag_spec {n} [IndexType n] (A : M) :
    VectorType.vequiv (diag A)
    =
    let A := mequiv A
    A.diag

  /-- Add outer product of a vector to a matrix.

  `outerprodselfAdd a x A = a•(x*xᴴ) + A`  (`xᴴ = xᵀ` for real vectors)

  Impementable using BLAS `her`, `hpr`, `syr`, `spr`. -/
  outerprodselfAdd (alpha : K) (x : X) (A : M) : M

  outerprodselfAdd_spec (alpha : K) (x : X) (A : M) :
    mequiv (outerprodselfAdd alpha x A)
    =
    let x := (Matrix.col (Fin 1) (VectorType.vequiv x))
    alpha • (x * xᴴ) + mequiv A

  /-- Add symmetric outer product of two vectors to a matrix.

  `outerprodselfAdd a x A = a•(x*yᴴ) + (y*(a•x)ᴴ) + A`  (`xᴴ = xᵀ` for real vectors)

  Impementable using BLAS `ger`, `geru`, `gerc`. -/
  outerprodsymmAdd (alpha : K) (x y : X) (A : M) : M

  outerprodsymmAdd_spec (alpha : K) (x y : X) (A : M) :
    mequiv (outerprodAdd alpha x y A)
    =
    let x := (Matrix.col (Fin 1) (VectorType.vequiv x))
    alpha • (x * xᴴ) + (x * (alpha • x)ᴴ) + mequiv A


namespace DenseMatrixType

export DenseMatrixType.Square (diagonal diagonal_spec diag diag_spec)

attribute [matrix_to_spec, matrix_from_spec ←]
  diagonal_spec diag_spec

section Instances

variable
  {M : Type*}
  {n : Type*} [IndexType n] [DecidableEq n]
  {R K : Type*} [RealScalar R] [Scalar R K]
  {X : Type*} [VectorType.Base X n K]
  [DenseMatrixType.Base M X X]
  [DenseMatrixType.Square M X]


instance : One M := ⟨diagonal (VectorType.const 1)⟩

@[matrix_to_spec, matrix_from_spec ←]
theorem one_spec : mequiv (1 : M) = (1 : Matrix n n K) := by
  conv => lhs; dsimp [One.one, OfNat.ofNat]
  simp[matrix_to_spec,vector_to_spec]
  rfl

end Instances
