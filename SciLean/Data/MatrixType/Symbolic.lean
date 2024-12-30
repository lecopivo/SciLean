import SciLean.Data.MatrixType.Base

/-!

This file contains functions with matrix types that should be considered only symbolically.

Operations like determinant or matrix inverse are computationally expensive and there is no
universal algorithm for them. Often they are computed only approximately.

-/

namespace SciLean

namespace DenseMatrixType


section SquareMatrices

variable
  {R K} [RealScalar R] [Scalar R K]
  {n : Type u} [IndexType n] [DecidableEq n]
  {X} [VectorType.Base X n K]
  {M} [DenseMatrixType.Base M X X]


/-- Deteminant of a matrix.

It is computable but you really do not want to run it so we disable it.
-/
noncomputable
def det (A : M) : K :=
  let A := mequiv A
  A.det

/-- Inverse of a matrix. -/
noncomputable
def inv (A : M) : M :=
  let A := mequiv A
  mequiv.symm (A⁻¹)

#check Matrix.inv

def IsInvertible (A : M) : Prop :=
  let A := mequiv A
  IsUnit A

open Matrix in
/-- Solve linear system of equations `A*x = b`. -/
noncomputable
def linSolve (A : M) (b : X) : X :=
  let A := mequiv A
  let b := VectorType.Base.vequiv b
  VectorType.Base.vequiv.symm (A⁻¹ *ᵥ b)

end SquareMatrices
