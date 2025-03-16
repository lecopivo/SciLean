import SciLean.Algebra.TensorProduct.Basic
import SciLean.Algebra.TensorProduct.MatMul
import SciLean.Data.DataArray.DataArray

import SciLean.Analysis.Scalar.FloatAsReal

namespace SciLean

variable
  {R : Type*} [RealScalar R] [PlainDataType R]
  [BLAS (DataArray R) R R] [LawfulBLAS (DataArray R) R R]
  {I nI} [IdxType I nI] {J nJ} [IdxType J nJ] {K nK} [IdxType K nK]


instance : TensorProductType R (R^[I]) (R^[J]) (R^[I,J]) where
  equiv := ⟨fun _ => True, sorry_proof⟩ -- TODO: provide proper implementation of the equivalence
  tmulAdd a y x A :=
    -- I do not understant why I should call it this way, it seems that x and y are swapped ...
    let A := BLAS.LevelTwoData.ger .RowMajor nJ nI a x.1 0 1 y.1 0 1 A.1 0 nJ
    -- for some reason this is incorrect
    -- let A := BLAS.LevelTwoData.ger .RowMajor nm nn a y.1 0 1 x.1 0 1 A.1 0 nn
    ⟨A, sorry_proof⟩
  matVecMul a A x b y :=
    let y := BLAS.LevelTwoData.gemv .RowMajor .NoTrans
      nJ nI a A.1 0 nJ x.1 0 1 b y.1 0 1
    ⟨y, sorry_proof⟩
  matHVecMul a A y b x :=
    let x := BLAS.LevelTwoData.gemv .RowMajor .ConjTrans
      nJ nI a A.1 0 nJ y.1 0 1 b x.1 0 1
    ⟨x, sorry_proof⟩
  tmulAdd_eq_tmul := sorry_proof


instance : TensorProductMul R (R^[I]) (R^[K]) (R^[J]) (R^[I,K]) (R^[K,J]) (R^[I,J]) where
  matMul := sorry -- todo: update LeanBLAS with level 3 functions


instance : TensorProductGetYX R (R^[I]) (R^[J]) (R^[I,J]) := ⟨⟩
instance : TensorProductGetY R (R^[I]) (R^[J]) (R^[I,J]) := ⟨⟩
instance : TensorProductGetX R (R^[I]) (R^[J]) (R^[I,J]) := ⟨⟩
instance : TensorProductGetRXY R (R^[I]) (R^[J]) (R^[I,J]) := ⟨⟩


variable (A : R^[10,20]) (B : R^[20,5]) (x : R^[5])

#check A*B*x
