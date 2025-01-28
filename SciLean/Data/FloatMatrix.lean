import SciLean.Data.VectorType.Base
import SciLean.Data.MatrixType.Base
import SciLean.Data.MatrixType.Dense
import SciLean.Data.MatrixType.Square
import SciLean.Data.MatrixType.MatMul
import SciLean.Data.MatrixType.Basic
import SciLean.Data.FloatVector
import SciLean.Data.DataArray.PlainDataType

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

structure FloatMatrix' (ord : BLAS.Order) (storage : DenseMatrix.Storage) (m n : Type*) [IndexType m] [IndexType n] where
  data : DenseMatrix FloatArray ord storage (size m) (size n) Float

-- abbrev FloatMatrix (n : Type*) [IndexType n] := FloatMatrix' DenseMatrix.packedStorage n

namespace FloatVector

variable
  {strg : DenseMatrix.Storage}
  {k m n : Type*} {_ : IndexType k} {_ : IndexType m} {_ : IndexType n}

instance : VectorType.Base (FloatMatrix' ord strg m n) (m×n) Float where
  toVec A := fun (i,j) => A.data.get (toFin i) (toFin j)
  zero := ⟨DenseMatrix.const (Array:=FloatArray) (size m) (size n) strg 0.0⟩
  zero_spec := sorry_proof
  scal k x := ⟨x.data.scal k⟩
  scal_spec := sorry_proof
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
  conj x := x
  conj_spec := sorry_proof
  axpy a x y := ⟨DenseMatrix.axpy a x.data y.data⟩
  axpy_spec := sorry_proof
  axpby a x b y := ⟨DenseMatrix.axpby a x.data b y.data⟩
  axpby_spec := sorry_proof
  mul x y := ⟨DenseMatrix.mul x.data y.data⟩
  mul_spec := sorry_proof


instance : VectorType.Dense (FloatMatrix' ord strg m n) where
  fromVec f := ⟨DenseMatrix.ofFn (fun (i : Fin (size m)) (j : Fin (size n)) => f (fromFin i, fromFin j))⟩
  right_inv := by intro f; simp[VectorType.toVec]
  set := fun x (i,j) v => ⟨x.data.set (toFin i) (toFin j) v⟩
  set_spec := sorry_proof
  const k := ⟨DenseMatrix.const _ _ _ k⟩
  const_spec := sorry_proof
  scalAdd a b x := ⟨x.data.scalAdd a b⟩
  scalAdd_spec := sorry_proof
  div x y := ⟨DenseMatrix.div x.data y.data⟩
  div_spec := sorry_proof
  inv x := ⟨DenseMatrix.inv x.data⟩
  inv_spec := sorry_proof
  exp x := ⟨DenseMatrix.exp x.data⟩
  exp_spec := sorry_proof


instance : VectorType.Lawful (FloatMatrix' ord .normal m n) where
  toVec_injective :=  sorry_proof


-- Because `MatrixType.Base` has `X` and `Y` as `outParam` we are forced to pick particular
-- storage option for input and output vectors ... this does not look ideal
instance : MatrixType.Base (FloatMatrix' ord strg m n) (FloatVector n) (FloatVector m) where

  toMatrix A i j:= A.data.get (toFin i) (toFin j)
  toVec_eq_toMatrix := by intros; rfl
  row A i := ⟨A.data.row (toFin i) |>.toNormal⟩
  row_spec := sorry_proof
  sumRows A := ⟨.ofFn fun i => (A.data.row i).sum⟩
  sumRows_spec := sorry_proof
  col A j := ⟨A.data.col (toFin j) |>.toNormal⟩
  col_spec := sorry_proof
  sumCols A := ⟨.ofFn fun j => (A.data.col j).sum⟩
  sumCols_spec := sorry_proof
  gemv a b A x y := ⟨DenseMatrix.gemv a A.data x.data b y.data⟩
  gemv_spec := sorry_proof
  gemvT a b A x y := ⟨DenseMatrix.gemvT a A.data x.data b y.data⟩
  gemvT_spec := sorry_proof
  gemvH a b A x y := ⟨DenseMatrix.gemvH a A.data x.data b y.data⟩
  gemvH_spec := sorry_proof


instance : MatrixType.Dense (FloatMatrix' ord strg m n) where
  fromMatrix f := ⟨DenseMatrix.ofFn fun i j => f (fromFin i) (fromFin j)⟩
  set' A i j v := ⟨A.data.set (toFin i) (toFin j) v⟩
  set'_spec := by simp[VectorType.set, MatrixType.set']
  right_inv' := by intro A; simp[MatrixType.toMatrix]
  updateRow A i x :=
    let A := A.data.row (toFin i) |>.setArray x.data
    ⟨⟨A.data, sorry_proof⟩⟩
  updateRow_spec := sorry_proof
  updateCol A j y :=
    let A := A.data.col (toFin j) |>.setArray y.data
    ⟨⟨A.data, sorry_proof⟩⟩
  updateCol_spec := sorry_proof
  outerprodAdd a x y A := ⟨DenseMatrix.ger a x.data y.data A.data⟩
  outerprodAdd_spec := sorry_proof


instance : MatrixType.Square (FloatMatrix' ord strg n n) where
  diagonal x := ⟨DenseMatrix.diag x.data⟩
  diagonal_spec := sorry_proof
  diag A := ⟨A.data.diagonal⟩
  diag_spec := sorry_proof


-- instance : MatrixType.MatMul (FloatMatrix' strg m n) (FloatMatrix' strg k m) (FloatMatrix' strg k n) where
--   matmul := sorry_proof
--   matmul_spec := sorry_proof

instance : MatrixType (FloatMatrix' ord .normal) FloatVector where

instance : ToString (FloatMatrix' ord strg n m) := ⟨fun A => A.data.toString⟩

instance : PlainDataType (FloatMatrix' ord .normal n m) where
  btype := .inr {
    bytes := (size m * size n * 8).toUSize
    h_size := sorry_proof
    fromByteArray arr i _ :=
      let size := size m * size n * 8
      let r := ByteArray.copySlice arr i.toNat (ByteArray.mkEmpty 0) 0 size
      ⟨⟨r.toFloatArray sorry_proof,sorry_proof⟩⟩ -- unsafe cast here
    toByteArray arr i _ A :=
      let size := size m * size n * 8
      let v' : ByteArray := A.data.data.toByteArray
      ByteArray.copySlice v' 0 arr i.toNat size
    toByteArray_size := sorry_proof
    fromByteArray_toByteArray := sorry_proof
    fromByteArray_toByteArray_other := sorry_proof
  }
