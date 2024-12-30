import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.RowCol
import SciLean.Data.IndexType

import SciLean.Analysis.Scalar
import SciLean.Analysis.AdjointSpace.Basic
import SciLean.Analysis.Convenient.SemiInnerProductSpace

import SciLean.Data.VectorType.Base
import SciLean.Data.MatrixType.Init

namespace SciLean

open Matrix VectorType

/-- `DenseMatrixType M X Y` says that `M` is a matrix transforming vectors of type `X` to vectors
of type `Y`.

This class provides functionality implementable using BLAS. -/
class DenseMatrixType.Base
      (M : Type*)
      {m n : outParam (Type*)} [IndexType m] [IndexType n]
      {R K : outParam (Type*)} [RealScalar R] [Scalar R K]
      (X Y : outParam (Type*)) [VectorType.Base X n K] [VectorType.Base Y m K]
  extends
    VectorType.Base M (m×n) K
  where

  mequiv : M ≃ Matrix m n K

  mequiv_eq_vequiv (A : M) : mequiv A = fun (i : m) (j : n) => vequiv A (i,j)

  /-    Level 1 like BLAS operations    -/

  -- TODO: This should return `SubMatrix m n (point i) id`
  /-- Get row of matrix -/
  row (A : M) (i : m) : X
  row_spec (A : M) (i : m) :
    VectorType.vequiv (row A i)
    =
    let A := mequiv A
    fun j => A i j

  /-- Sum rows of a matrix. -/
  sumRows (A : M) : Y
  sumRows_spec (A : M):
    VectorType.vequiv (sumRows A)
    =
    let A := mequiv A
    fun i => ∑ j, A i j

  /-- Update row, i.e. set row to a given vector. -/
  updateRow (A : M) (i : m) (x : X) : M
  updateRow_spec (A : M) (i : m) (x : X) [DecidableEq m] :
    mequiv (updateRow A i x)
    =
    let A := mequiv A
    let x := VectorType.vequiv x
    A.updateRow i x

  -- TODO: This should return `SubMatrix m n id (point j)`
  /-- Get column of matrix -/
  col (A : M) (j : n) : Y
  col_spec (A : M) (j : n) :
    VectorType.vequiv (col A j)
    =
    let A := (mequiv A)
    fun i => A i j

  /-- Sum columns of a matrix -/
  sumCols (A : M) : X
  sumCols_spec (A : M):
    VectorType.vequiv (sumCols A)
    =
    let A := mequiv A
    fun j => ∑ i, A i j

  /-- Update column, i.e. set column to a given vector. -/
  updateCol (A : M) (j : n) (y : Y) : M
  updateCol_spec (A : M) (j : n) (y : Y) [DecidableEq n] :
    mequiv (updateCol A i x)
    =
    let A := mequiv A
    let y := VectorType.vequiv y
    A.updateColumn j y


  /- Level 2 like BLAS operations -/

  /-- Matrix vector multiplication.

  Implementable using BLAS `gemv`. -/
  gemv (alpha beta : K) (A : M) (x : X) (y : Y) : Y

  gemv_spec (alpha beta : K) (A : M) (x : X) (y : Y) :
    VectorType.vequiv (gemv alpha beta A x y)
    =
    let A := mequiv A
    let x := VectorType.vequiv x
    let y := VectorType.vequiv y
    alpha • A *ᵥ x + beta • y

  /-- Transpose matrix vector multiplication.

  Implementable using BLAS `gemv`. -/
  gemvT (alpha beta : K) (A : M) (y : Y) (x : X) : X

  gemvT_spec (alpha beta : K) (A : M) (y : Y) (x : X) :
    VectorType.vequiv (gemvT alpha beta A y x)
    =
    let A := mequiv A
    let x := VectorType.vequiv x
    let y := VectorType.vequiv y
    alpha • Aᵀ *ᵥ y + beta • x


  /-- Conjugate transpose matrix vector multiplication.

  Implementable using BLAS `gemv`. -/
  gemvH (alpha beta : K) (A : M) (y : Y) (x : X) : X

  gemvH_spec (alpha beta : K) (A : M) (y : Y) (x : X) :
    VectorType.vequiv (gemvH alpha beta A y x)
    =
    let A := mequiv A
    let x := VectorType.vequiv x
    let y := VectorType.vequiv y
    alpha • Aᴴ *ᵥ y + beta • x


  /-- Add outer product of two vectors to a matrix

  `outerprdoAdd a y x A = a • y * xᴴ + A`

  Impementable using BLAS `ger`, `geru`, `gerc`. -/
  outerprodAdd (alpha : K) (y : Y) (x : X) (A : M) : M

  outerprodAdd_spec  (alpha : K) (y : Y) (x : X) (A : M) :
    mequiv (outerprodAdd alpha y x A)
    =
    let A := mequiv A
    let x := (Matrix.col (Fin 1) (VectorType.vequiv x))
    let y := (Matrix.col (Fin 1) (VectorType.vequiv y))
    alpha • (y * xᴴ) + A


namespace DenseMatrixType

export DenseMatrixType.Base (mequiv mequiv_eq_vequiv row row_spec sumRows sumRows_spec updateRow updateRow_spec
  col col_spec sumCols sumCols_spec updateCol updateCol_spec
  gemv gemv_spec gemvT gemvT_spec gemvH gemvH_spec outerprodAdd outerprodAdd_spec)

attribute [matrix_to_spec, matrix_from_spec ←] row_spec sumRows_spec updateRow_spec
  col_spec sumCols_spec updateCol_spec gemv_spec gemvT_spec gemvH_spec
  outerprodAdd_spec


section BasicOperations


variable
  {R K} [RealScalar R] [Scalar R K]
  {m n : Type*} [IndexType m] [IndexType n]
  {X Y} [VectorType.Base X n K] [VectorType.Base Y m K]
  {M} [DenseMatrixType.Base M X Y]


set_default_scalar K

open DenseMatrixType

@[matrix_to_spec, matrix_from_spec ←]
theorem add_spec (A B : M) : mequiv (A + B) = mequiv A + mequiv B := by
  funext i j
  simp[mequiv_eq_vequiv, vector_to_spec]

@[matrix_to_spec, matrix_from_spec ←]
theorem sub_spec (A B : M) : mequiv (A - B) = mequiv A - mequiv B := by
  funext i j
  simp[mequiv_eq_vequiv, vector_to_spec]

@[matrix_to_spec, matrix_from_spec ←]
theorem neg_spec (A : M) : mequiv (-A) = -mequiv A := by
  funext i j
  simp[mequiv_eq_vequiv, vector_to_spec]

@[matrix_to_spec, matrix_from_spec ←]
theorem smul_spec (a : K) (A : M) : mequiv (a • A) = a • mequiv A := by
  funext i j
  simp[mequiv_eq_vequiv, vector_to_spec]

@[matrix_to_spec, matrix_from_spec ←]
theorem zero_spec : mequiv (0 : M) = 0 := by
  funext i j
  simp[mequiv_eq_vequiv, vector_to_spec]

-- @[matrix_to_spec, matrix_from_spec ←]
-- theorem inner_spec (A B : M) : ⟪A, B⟫ = ⟪(WithLp.equiv 2 (Matrix m n K)).symm (mequiv A), (WithLp.equiv 2 (Matrix m n K)).symm (equiv B)⟫ := by
--   simp only [inner, dot, matrix_to_spec]

-- @[matrix_to_spec, matrix_from_spec ←]
-- theorem norm_spec (A : M) : ‖A‖ = ‖mequiv A‖ := by
--   simp only [norm, Norm.norm, Scalar.toReal, nrm2, matrix_to_spec]

-- @[matrix_to_spec, matrix_from_spec ←]
-- theorem dist_spec (A B : M) : dist A B = ‖mequiv A - mequiv B‖ := by
--   simp only [dist, Norm.dist, norm, Norm.norm, Scalar.toReal, nrm2, matrix_to_spec]

end BasicOperations


section AlgebraicInstances


variable
  {R K} [RealScalar R] [Scalar R K]
  {m n : Type*} [IndexType m] [IndexType n]
  {X Y} [VectorType.Base X n K] [VectorType.Base Y m K]
  {M} [DenseMatrixType.Base M X Y]

open DenseMatrixType

/-- Linear equivalence between matrix type `M` and `Matrix m n K` -/
def mequivₗ : M ≃ₗ[K] (Matrix m n K) :=
  LinearEquiv.mk ⟨⟨mequiv,by simp only [matrix_to_spec,implies_true]⟩,by simp[matrix_to_spec]⟩
    mequiv.symm (mequiv.left_inv) (mequiv.right_inv)

/-- Continuous linear equivalence between matrix type `M` and `Matrix m n K` -/
def mequivL : M ≃L[K] (Matrix m n K) := ContinuousLinearEquiv.mk mequivₗ (by sorry_proof) (by sorry_proof)


instance : FiniteDimensional K (M) :=
   FiniteDimensional.of_injective (V₂:=Matrix m n K) mequivₗ.1
  (mequivₗ.left_inv.injective)


variable (M)
noncomputable
def basis : Basis (m×n) K (M) := Basis.ofEquivFun (ι:=m×n) (R:=K) (M:=M)
  (mequivₗ.trans (LinearEquiv.curry K K m n).symm)
variable {M}


@[simp, simp_core]
theorem finrank_eq_index_card : Module.finrank K (M) = Fintype.card m * Fintype.card n := by
  rw[Module.finrank_eq_card_basis (basis M)]
  simp only [Fintype.card_prod]


end AlgebraicInstances

end DenseMatrixType

end SciLean
