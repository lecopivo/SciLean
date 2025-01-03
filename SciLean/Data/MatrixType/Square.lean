import SciLean.Data.MatrixType.Base

namespace SciLean

open Matrix MatrixType VectorType
class MatrixType.Square
      (M : Type*)
      {n : outParam (Type*)} {_ : outParam (IndexType n)}
      {R K : outParam (Type*)} {_ : outParam (RealScalar R)} {_ : outParam (Scalar R K)}
      {X : outParam (Type*)} [VectorType.Base X n K]
      [MatrixType.Base M X X]
  where

  /-- Turn vector `x` into diagonal matrix -/
  diagonal (x : X) : M
  diagonal_spec (x : X) [DecidableEq n] :
    toMatrix (diagonal x)
    =
    let x := toVec x
    Matrix.diagonal x

  /-- Extract diagonal of matrix -/
  diag (A : M) : X
  diag_spec (A : M) :
    toVec (diag A)
    =
    let A := toMatrix A
    A.diag

  -- /-- Add outer product of a vector to a matrix.

  -- `outerprodselfAdd a x A = a•(x*xᴴ) + A`  (`xᴴ = xᵀ` for real vectors)

  -- Impementable using BLAS `her`, `hpr`, `syr`, `spr`. -/
  -- outerprodselfAdd (alpha : K) (x : X) (A : M) : M

  -- outerprodselfAdd_spec (alpha : K) (x : X) (A : M) :
  --   toMatrix (outerprodselfAdd alpha x A)
  --   =
  --   let x := Matrix.col (Fin 1) (toVec x)
  --   alpha • (x * xᴴ) + toMatrix A

  -- /-- Add symmetric outer product of two vectors to a matrix.

  -- `outerprodselfAdd a x A = a•(x*yᴴ) + (y*(a•x)ᴴ) + A`  (`xᴴ = xᵀ` for real vectors)

  -- Impementable using BLAS `ger`, `geru`, `gerc`. -/
  -- outerprodsymmAdd (alpha : K) (x y : X) (A : M) : M

  -- outerprodsymmAdd_spec (alpha : K) (x y : X) (A : M) :
  --   toMatrix (outerprodsymmAdd alpha x y A)
  --   =
  --   let x := (Matrix.col (Fin 1) (toVec x))
  --   alpha • (x * xᴴ) + (x * (alpha • x)ᴴ) + toMatrix A


namespace MatrixType

export MatrixType.Square (diagonal diagonal_spec diag diag_spec)

attribute [matrix_to_spec, matrix_from_spec ←]
  diagonal_spec diag_spec

section Instances

variable
  {M : Type*}
  {n : Type*} {_ : IndexType n}
  {R K : Type*} {_ : RealScalar R} {_ : Scalar R K}
  {X : Type*} [VectorType.Base X n K] [VectorType.Dense X]
  [MatrixType.Base M X X]
  [MatrixType.Square M]


instance : One M := ⟨diagonal (VectorType.const 1)⟩

open Classical in
@[matrix_to_spec, matrix_from_spec ←]
theorem one_spec : toMatrix (1 : M) = (1 : Matrix n n K) := by
  conv => lhs; dsimp [One.one, OfNat.ofNat]
  simp[matrix_to_spec,vector_to_spec]
  rfl

end Instances
