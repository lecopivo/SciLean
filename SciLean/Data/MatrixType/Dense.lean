import SciLean.Data.MatrixType.Base

namespace SciLean

open Matrix VectorType

open Function MatrixType.Base in
class MatrixType.Dense
    (M : Type*)
    {m n : outParam (Type*)} {_ : outParam (IndexType m)} {_ : outParam (IndexType n)}
    {R K : outParam (Type*)} {_ : outParam (RealScalar R)} {_ : outParam (Scalar R K)}
    {X Y : outParam (Type*)} {_ : outParam (VectorType.Base X n K)} {_ : outParam (VectorType.Base Y m K)}
    [MatrixType.Base M X Y]
  extends
    VectorType.Dense M
  where

  -- maybe it should be `Matrix m n K → M → M` such that `Dense` works also for submatrices
  -- the current definition forces lawfulness which excludes submatrices
  fromMatrix (f : Matrix m n K) : M
  -- protected left_inv'  : LeftInverse fromMatrix MatrixType.Base.toMatrix
  protected right_inv' : RightInverse fromMatrix MatrixType.Base.toMatrix

  /-- Set element at `(i,j)` to `v`. -/
  set' (A : M) (i : m) (j : n) (v : K) : M
  set'_spec (A : M) (i : m) (j : n) (v : K) :
    set' A i j v = VectorType.set A (i,j) v

  /-    Row and column operations    -/
  /- Setting rows and columns is found in `MatrixType.Dense` -/

  -- TODO: This should return `SubMatrix m n (point i) id`
  /-- Get row of matrix -/
  row (A : M) (i : m) : X
  row_spec (A : M) (i : m) :
    VectorType.toVec (row A i)
    =
    let A := toMatrix A
    fun j => A i j

  /-- Sum rows of a matrix. -/
  sumRows (A : M) : Y
  sumRows_spec (A : M):
    VectorType.toVec (sumRows A)
    =
    let A := toMatrix A
    fun i => ∑ j, A i j

  -- TODO: This should return `SubMatrix m n id (point j)`
  /-- Get column of matrix -/
  col (A : M) (j : n) : Y
  col_spec (A : M) (j : n) :
    VectorType.toVec (col A j)
    =
    let A := (toMatrix A)
    fun i => A i j

  /-- Sum columns of a matrix -/
  sumCols (A : M) : X
  sumCols_spec (A : M):
    VectorType.toVec (sumCols A)
    =
    let A := toMatrix A
    fun j => ∑ i, A i j


  /-- Update row, i.e. set row to a given vector. -/
  updateRow (A : M) (i : m) (x : X) : M
  updateRow_spec (A : M) (i' : m) (x : X) [DecidableEq m] :
    toVec (updateRow A i' x)
    =
    fun (i,j) =>
      let A := toMatrix A
      let x := VectorType.toVec x
      A.updateRow i' x i j


  /-- Update column, i.e. set column to a given vector. -/
  updateCol (A : M) (j : n) (y : Y) : M
  updateCol_spec (A : M) (j' : n) (y : Y) [DecidableEq n] :
    toVec (updateCol A j' y)
    =
    fun (i,j) =>
      let A := toMatrix A
      let y := toVec y
      A.updateCol j' y i j


  /-- Add outer product of two vectors to a matrix

  `outerprdoAdd a y x A = a • y * xᴴ + A`

  Impementable using BLAS `ger`, `geru`, `gerc`. -/
  outerprodAdd (alpha : K) (y : Y) (x : X) (A : M) : M

  outerprodAdd_spec  (alpha : K) (y : Y) (x : X) (A : M) :
    toVec (outerprodAdd alpha y x A)
    =
    fun (i,j) =>
      let A := toMatrix A
      let x := (Matrix.col (Fin 1) (toVec x))
      let y := (Matrix.col (Fin 1) (toVec y))
      (alpha • (y * xᴴ) + A) i j


namespace MatrixType

export MatrixType.Dense (fromMatrix
  row row_spec sumRows sumRows_spec col col_spec sumCols sumCols_spec
  updateRow updateRow_spec updateCol updateCol_spec outerprodAdd
  outerprodAdd_spec set' set'_spec)

attribute [vector_to_spec]
  row_spec sumRows_spec
  col_spec sumCols_spec
  updateRow_spec
  updateCol_spec
  outerprodAdd_spec


section Operations

variable
  {R K : Type*} {_ : RealScalar R} {_ : Scalar R K}
  {m n : Type*} {_ : IndexType m} {_ : IndexType n}
  {X Y : Type*} {_ : VectorType.Base X n K} {_ : VectorType.Base Y m K}
  {M} [MatrixType.Base M X Y] [Lawful M] [MatrixType.Dense M]

def updateElem (A : M) (i : m) (j : n) (f : K → K) : M :=
  let aij := toMatrix A i j
  MatrixType.set' A i j (f aij)

end Operations


section Equivalences

variable
  {R K : Type*} {_ : RealScalar R} {_ : Scalar R K}
  {m n : Type*} {_ : IndexType m} {_ : IndexType n}
  {X Y : Type*} {_ : VectorType.Base X n K} {_ : VectorType.Base Y m K}
  {M} [MatrixType.Base M X Y] [Lawful M] [MatrixType.Dense M]

open MatrixType

/-- Equivalence between matrix type `M` and `Matrix m n K` -/
def mequiv : M ≃ Matrix m n K where
  toFun := toMatrix
  invFun := fromMatrix
  left_inv := by
    have h : (toMatrix : M → (Matrix m n K)).Bijective := by
      constructor
      · apply toMatrix_injective
      · apply Dense.right_inv'.surjective
    intro x
    sorry_proof -- this should be true
  right_inv := MatrixType.Dense.right_inv'

@[matrix_to_spec]
theorem mequiv_apply_eq_toMatrix (A : M) : mequiv A = toMatrix A := rfl

@[matrix_to_spec]
theorem mequiv_symm_apply_eq_fromMatrix (f : m → n → K) : mequiv.symm f = fromMatrix (M:=M) f := rfl

@[simp, simp_core]
theorem fromMatrix_toMatrix (A : M) :
    fromMatrix (toMatrix A) = A := by
  rw[← mequiv_apply_eq_toMatrix, ← mequiv_symm_apply_eq_fromMatrix]
  simp only [Equiv.symm_apply_apply]

omit [Lawful M] in
@[simp, simp_core]
theorem toMatrix_fromMatrix (f : m → n → K) :
    toMatrix (fromMatrix (M:=M) f) = f := by
  rw[MatrixType.Dense.right_inv']

@[vector_to_spec]
theorem fromMatrix_eq_fromVec {f : Matrix m n K} :
    fromMatrix (M:=M) f = VectorType.fromVec fun (i,j) => f i j := by
  apply toMatrix_injective
  conv => rhs; simp only [toMatrix_eq_toVec]
  simp

/-- Linear equivalence between matrix type `M` and `Matrix m n K` -/
def mequivₗ : M ≃ₗ[K] (Matrix m n K) :=
  LinearEquiv.mk ⟨⟨mequiv,by simp only [matrix_to_spec,implies_true]⟩,by simp[matrix_to_spec]⟩
    mequiv.symm (mequiv.left_inv) (mequiv.right_inv)

/-- Continuous linear equivalence between matrix type `M` and `Matrix m n K` -/
def mequivL : M ≃L[K] (Matrix m n K) := ContinuousLinearEquiv.mk mequivₗ (by sorry_proof) (by sorry_proof)


instance (priority:=low) : FiniteDimensional K (M) :=
   FiniteDimensional.of_injective (V₂:=Matrix m n K) mequivₗ.1
  (mequivₗ.left_inv.injective)


variable (M)
noncomputable
def basis : _root_.Basis (m×n) K (M) := Basis.ofEquivFun (ι:=m×n) (R:=K) (M:=M)
  (mequivₗ.trans (LinearEquiv.curry K K m n).symm)
variable {M}


@[simp, simp_core]
theorem finrank_eq_index_card : Module.finrank K (M) = Fintype.card m * Fintype.card n := by
  rw[Module.finrank_eq_card_basis (basis M)]
  simp only [Fintype.card_prod]


end Equivalences

end MatrixType

end SciLean
