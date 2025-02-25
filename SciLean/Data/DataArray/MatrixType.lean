import SciLean.Data.DataArray.VectorType
import SciLean.Data.MatrixType.Base
import SciLean.Data.MatrixType.Dense
import SciLean.Data.MatrixType.Square
import SciLean.Data.MatrixType.MatMul

import LeanBLAS

namespace SciLean

open BLAS


----------------------------------------------------------------------------------------------------
-- MatrixType instances ----------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

open IndexType in
instance {m n R K : Type*}
    [IndexType m] [IndexType n] [PlainDataType K]
    [RealScalar R] [Scalar R K]
    [BLAS (DataArray K) R K] [LawfulBLAS (DataArray K) R K]  :
    MatrixType.Base (K^[m,n]) (K^[n]) (K^[m]) where
  toMatrix A i j := A[i,j]
  toVec_eq_toMatrix := by intros; rfl
  gemv a b A x y :=
    let y := BLAS.LevelTwoData.gemv .RowMajor .NoTrans
      (size m) (size n) a A.1 0 (size n) x.1 0 1 b y.1 0 1
    ⟨y, sorry_proof⟩
  gemv_spec := sorry_proof
  gemvT a b A x y :=
    -- am I calling this right?
    let y := BLAS.LevelTwoData.gemv .RowMajor .Trans
      (size m) (size n) 1 A.1 0 (size n) x.1 0 1 0 y.1 0 1
    ⟨y, sorry_proof⟩
  gemvT_spec := sorry_proof
  gemvH a b A x y :=
    let y := BLAS.LevelTwoData.gemv .RowMajor .ConjTrans
      (size m) (size n) 1 A.1 0 (size n) x.1 0 1 0 y.1 0 1
    ⟨y, sorry_proof⟩
  gemvH_spec := sorry_proof


open IndexType in
instance {m n R K : Type*}
    [IndexType m] [IndexType n] [PlainDataType K]
    [RealScalar R] [Scalar R K]
    [BLAS (DataArray K) R K] [LawfulBLAS (DataArray K) R K]  :
    MatrixType.Dense (K^[m,n]) where
  fromMatrix f := ⊞ i j => f i j
  right_inv' := sorry_proof
  set' A i j v := A.set (i,j) v
  set'_spec := sorry_proof
  row A i := A.curry[i]
  row_spec := sorry_proof
  sumRows A :=
    ⊞ (i : m) => BLAS.LevelOneDataExt.sum (size n) A.1 (toFin i * size n) 1
  sumRows_spec := sorry_proof
  col A j :=
    let c := BLAS.LevelOneData.copy (size m) A.1 (toFin j) (size n) (panic "col for R^[m,n] not implented!") 0 1
    ⟨c, sorry_proof⟩
  col_spec := sorry_proof
  sumCols A :=
    ⊞ (j : n) => BLAS.LevelOneDataExt.sum (size m) A.1 (toFin j) (size n)
  sumCols_spec := sorry_proof
  updateRow A i r :=
    let A := BLAS.LevelOneData.copy (size n) r.1 0 1 A.1 (toFin i * size n) 1
    ⟨A, sorry_proof⟩
  updateRow_spec := sorry_proof
  updateCol A j c :=
    let A := BLAS.LevelOneData.copy (size m) c.1 0 1 A.1 (toFin j) (size n)
    ⟨A, sorry_proof⟩
  updateCol_spec := sorry_proof
  outerprodAdd a x y A :=
    let A := BLAS.LevelTwoData.ger .RowMajor (size m) (size n) a x.1 0 1 y.1 0 1 A.1 0 (size n)
    ⟨A, sorry_proof⟩
  outerprodAdd_spec := sorry_proof
