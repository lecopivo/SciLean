import SciLean.Data.VectorType.Base
import SciLean.Data.MatrixType.Base
import SciLean.Data.MatrixType.Dense
import SciLean.Data.MatrixType.Square
import SciLean.Data.MatrixType.MatMul
import SciLean.Data.FloatVector

import LeanBLAS.Matrix.DenseMatrix

namespace SciLean

open BLAS IndexType

section BLASMissing

-- def _root_.BLAS.DenseMatrix.packedStorage : DenseMatrix.Storage where
--   order := .RowMajor
--   offset := 0
--   lda :=
--   bufferSize := .exact

end BLASMissing

structure FloatMatrix' (storage : DenseMatrix.Storage) (m n : Type*) [IndexType m] [IndexType n] where
  data : DenseMatrix FloatArray storage (size m) (size n) Float

-- abbrev FloatMatrix (n : Type*) [IndexType n] := FloatMatrix' DenseMatrix.packedStorage n

namespace FloatVector

variable
  {strg : DenseMatrix.Storage}
  {k m n : Type*} [IndexType k] [IndexType m] [IndexType n]

instance : VectorType.Base (FloatMatrix' strg m n) (m×n) Float where
  toVec A := fun (i,j) => A.data.get (toFin i) (toFin j)
  zero := ⟨DenseMatrix.const (Array:=FloatArray) (size m) (size n) strg 0.0⟩
  zero_spec := sorry_proof
  scal k x := ⟨x.data.scal k⟩
  scal_spec := sorry_proof
  scalAdd a b x := ⟨x.data.scalAdd a b⟩
  scalAdd_spec := sorry_proof
  sum x := x.data.sum
  sum_spec := sorry_proof
  asum x := x.data.asum
  asum_spec := sorry_proof
  nrm2 x := x.data.nrm2
  nrm2_spec := sorry_proof
  iamax x :=
    let (i,j) := x.data.iamax
    (fromFin i, fromFin j)
  iamax_spec := sorry_proof
  imaxRe x h :=
    let (i,j) := x.data.imaxRe (by simp_all)
    (fromFin i, fromFin j)
  imaxRe_spec := sorry_proof
  iminRe x h :=
    let (i,j) := x.data.iminRe (by simp_all)
    (fromFin i, fromFin j)
  iminRe_spec := sorry_proof
  dot x y := x.data.dot y.data
  dot_spec := sorry_proof
  axpy a x y := ⟨DenseMatrix.axpy a x.data y.data⟩
  axpy_spec := sorry_proof
  axpby a x b y := ⟨DenseMatrix.axpby a x.data b y.data⟩
  axpby_spec := sorry_proof
  mul x y := ⟨DenseMatrix.mul x.data y.data⟩
  mul_spec := sorry_proof


instance : VectorType.Dense (FloatMatrix' strg m n) where
  fromVec f := ⟨DenseMatrix.ofFn (fun (i : Fin (size m)) (j : Fin (size n)) => f (fromFin i, fromFin j))⟩
  right_inv := by intro f; simp[VectorType.toVec]
  const k := ⟨DenseMatrix.const _ _ _ k⟩
  const_spec := sorry
  div x y := ⟨DenseMatrix.div x.data y.data⟩
  div_spec := sorry
  inv x := ⟨DenseMatrix.inv x.data⟩
  inv_spec := sorry
  exp x := ⟨DenseMatrix.exp x.data⟩
  exp_spec := sorry



-- Because `MatrixType.Base` has `X` and `Y` as `outParam` we are forced to pick particular
-- storage option for input and output vectors ... this does not look ideal
instance : MatrixType.Base (FloatMatrix' strg m n) (FloatVector n) (FloatVector m) where

  toMatrix A i j:= A.data.get (toFin i) (toFin j)
  toVec_eq_toMatrix := by intros; rfl
  row A i := ⟨A.data.row (toFin i)⟩
  row_spec := sorry_proof
  sumRows A := ⟨A.data.sumRows⟩
  sumRows_spec := sorry_proof
  col A j := ⟨A.data.col (toFin j)⟩
  col_spec := sorry
  sumCols A := ⟨A.data.sumCols⟩
  sumCols_spec := sorry
  gemv a b A x y := ⟨DenseMatrix.gemv a A.data x.data b y.data⟩
  gemv_spec := sorry
  gemvT a b A x y := ⟨DenseMatrix.gemvT a A.data x.data b y.data⟩
  gemvT_spec := sorry
  gemvH a b A x y := ⟨DenseMatrix.gemvH a A.data x.data b y.data⟩
  gemvH_spec := sorry


instance : MatrixType.Dense (FloatMatrix' strg m n) where
  fromMatrix f := ⟨DenseMatrix.ofFn fun i j => f (fromFin i) (fromFin j)⟩
  right_inv' := by intro A; simp[MatrixType.toMatrix]
  updateRow A i x := ⟨DenseMatrix.rowSet A.data (toFin i) x.data⟩
  updateRow_spec := sorry
  updateCol A j y := ⟨DenseMatrix.colSet A.data (toFin j) y.data⟩
  updateCol_spec := sorry
  outerprodAdd a x y A := ⟨DenseMatrix.ger a x.data y.data A.data⟩
  outerprodAdd_spec := sorry


instance : MatrixType.Square (FloatMatrix' strg n n) where
  diagonal x := ⟨DenseMatrix.diag x.data⟩
  diagonal_spec := sorry
  diag A := ⟨A.data.diagonal⟩
  diag_spec := sorry


-- instance : MatrixType.MatMul (FloatMatrix' strg m n) (FloatMatrix' strg k m) (FloatMatrix' strg k n) where
--   matmul := sorry
--   matmul_spec := sorry
