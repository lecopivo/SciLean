-- import SciLean.Data.DataArray.VectorType
-- import SciLean.Data.MatrixType.Base
-- import SciLean.Data.MatrixType.Dense
-- import SciLean.Data.MatrixType.Square
-- import SciLean.Data.MatrixType.MatMul

-- import LeanBLAS

namespace SciLean

-- open BLAS


-- ----------------------------------------------------------------------------------------------------
-- -- MatrixType instances ----------------------------------------------------------------------------
-- ----------------------------------------------------------------------------------------------------

-- open IndexType in
-- instance {m n R K : Type*}
--     {nm} [IndexType m nm] {nn} [IndexType n nn] [PlainDataType K]
--     [RealScalar R] [Scalar R K]
--     [BLAS (DataArray K) R K] [LawfulBLAS (DataArray K) R K]  :
--     MatrixType.Base (K^[m,n]) (K^[n]) (K^[m]) where
--   toMatrix A i j := A[i,j]
--   toVec_eq_toMatrix := by intros; rfl
--   gemv a b A x y :=
--     let y := BLAS.LevelTwoData.gemv .RowMajor .NoTrans
--       nm nn a A.1 0 nn x.1 0 1 b y.1 0 1
--     ⟨y, sorry_proof⟩
--   gemv_spec := sorry_proof
--   gemvT a b A x y :=
--     -- am I calling this right?
--     let y := BLAS.LevelTwoData.gemv .RowMajor .Trans
--       nm nn a A.1 0 nn x.1 0 1 b y.1 0 1
--     ⟨y, sorry_proof⟩
--   gemvT_spec := sorry_proof
--   gemvH a b A x y :=
--     let y := BLAS.LevelTwoData.gemv .RowMajor .ConjTrans
--       nm nn a A.1 0 nn x.1 0 1 b y.1 0 1
--     ⟨y, sorry_proof⟩
--   gemvH_spec := sorry_proof


-- open IndexType in
-- instance {m n R K : Type*}
--     {nm} [IndexType m nm] {nn} [IndexType n nn] [PlainDataType K]
--     [RealScalar R] [Scalar R K]
--     [BLAS (DataArray K) R K] [LawfulBLAS (DataArray K) R K]
--     [Fold m] [Fold n] :
--     MatrixType.Dense (K^[m,n]) where
--   fromMatrix f := ⊞ i j => f i j
--   right_inv' := sorry_proof
--   set' A i j v := A.set (i,j) v
--   set'_spec := sorry_proof
--   row A i := A.curry[i]
--   row_spec := sorry_proof
--   sumRows A :=
--     ⊞ (i : m) => BLAS.LevelOneDataExt.sum nn A.1 ((toIdx i) * nn) 1
--   sumRows_spec := sorry_proof
--   col A j :=
--     let c : K^[m] := 0
--     let c := BLAS.LevelOneData.copy nm A.1 (toIdx j) nn c.1 0 1
--     ⟨c, sorry_proof⟩
--   col_spec := sorry_proof
--   sumCols A :=
--     ⊞ (j : n) => BLAS.LevelOneDataExt.sum nm A.1 (toIdx j) nn
--   sumCols_spec := sorry_proof
--   updateRow A i r :=
--     let A := BLAS.LevelOneData.copy nn r.1 0 1 A.1 (toIdx i * nn) 1
--     ⟨A, sorry_proof⟩
--   updateRow_spec := sorry_proof
--   updateCol A j c :=
--     let A := BLAS.LevelOneData.copy nm c.1 0 1 A.1 (toIdx j) nn
--     ⟨A, sorry_proof⟩
--   updateCol_spec := sorry_proof
--   outerprodAdd a x y A :=
--     -- I do not understant why I should call it this way, it seems that x and y are swapped ...
--     let A := BLAS.LevelTwoData.ger .RowMajor nn nm a y.1 0 1 x.1 0 1 A.1 0 nn

--     -- for some reason this is incorrect
--     -- let A := BLAS.LevelTwoData.ger .RowMajor nm nn a y.1 0 1 x.1 0 1 A.1 0 nn

--     ⟨A, sorry_proof⟩
--   outerprodAdd_spec := sorry_proof
