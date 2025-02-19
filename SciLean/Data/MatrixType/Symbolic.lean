import SciLean.Data.MatrixType.Base
import SciLean.Data.MatrixType.Dense

/-!

This file contains functions with matrix types that should be considered only symbolically.

Operations like determinant or matrix inverse are computationally expensive and there is no
universal algorithm for them. Often they are computed only approximately.

-/

namespace SciLean

namespace MatrixType


section SquareMatrices

variable
  {R K} {_ : RealScalar R} {_ : Scalar R K}
  {n} {_ : IndexType n}
  {X} {_ : VectorType.Base X n K}
  {M} [MatrixType.Base M X X]
  [DecidableEq n]


/-- Deteminant of a matrix.

It is computable but you really do not want to run it so we disable it.
-/
noncomputable
def det (A : M) : K :=
  let A := toMatrix A
  A.det

/-- Inverse of a matrix. -/
noncomputable
def inv [MatrixType.Dense M] (A : M) : M :=
  let A := toMatrix A
  fromMatrix (A⁻¹)

def IsInvertible (A : M) : Prop :=
  let A := toMatrix A
  IsUnit A

open Matrix VectorType in
/-- Solve linear system of equations `A*x = b`. -/
noncomputable
def linSolve [VectorType.Dense X] (A : M) (b : X) : X :=
  let A := toMatrix A
  let b := fun i : n => b[i]
  fromVec (A⁻¹ *ᵥ b)

end SquareMatrices
