import SciLean.Algebra.TensorProduct.Basic
import SciLean.Algebra.TensorProduct.Self
import SciLean.Algebra.TensorProduct.MatMul
import SciLean.Data.DataArray.DataArray

import SciLean.Analysis.Scalar.FloatAsReal

namespace SciLean

variable
  {R : Type u'} [RealScalar R] [PlainDataType R]
  [BLAS (DataArray R) R R] [LawfulBLAS (DataArray R) R R]
  {I : Type u} {nI} [IdxType I nI] {J : Type v} {nJ} [IdxType J nJ] {K: Type w} {nK} [IdxType K nK]



instance : TensorProductType R (R^[I]) (R^[J]) (R^[I,J]) where
  equiv := ⟨fun _ => True, sorry_proof⟩ -- TODO: provide proper implementation of the equivalence
  tmulAdd a y x A :=
    -- I do not understant why I should call it this way, it seems that x and y are swapped ...
    let A := BLAS.LevelTwoData.ger .RowMajor nJ nI a x.1 0 1 y.1 0 1 A.1 0 nJ
    -- for some reason this is incorrect
    -- let A := BLAS.LevelTwoData.ger .RowMajor nm nn a y.1 0 1 x.1 0 1 A.1 0 nn
    ⟨A, sorry_proof⟩
  matVecMulAdd a A x b y :=
    let y := BLAS.LevelTwoData.gemv .RowMajor .NoTrans
      nJ nI a A.1 0 nJ x.1 0 1 b y.1 0 1
    ⟨y, sorry_proof⟩
  matHVecMulAdd a A y b x :=
    let x := BLAS.LevelTwoData.gemv .RowMajor .ConjTrans
      nJ nI a A.1 0 nJ y.1 0 1 b x.1 0 1
    ⟨x, sorry_proof⟩
  tmulAdd_eq_tmul := sorry_proof


-- TODO: use BLAS `gemm`!!!
instance [IdxType.Fold'.{_,0} I] [IdxType.Fold'.{_,0} J] [IdxType.Fold' K] :
    TensorProductMul R (R^[I]) (R^[K]) (R^[J]) (R^[I,K]) (R^[K,J]) (R^[I,J]) where
  matMul a A B b C := ⊞ (i:I) (j:J) => b • C[i,j] + a • ∑ᴵ (k:K), A[i,k] * B[k,j]


instance : TensorProductGetYX R (R^[I]) (R^[J]) (R^[I,J]) := ⟨⟩
instance : TensorProductGetY R (R^[I]) (R^[J]) (R^[I,J]) := ⟨⟩
instance : TensorProductGetX R (R^[I]) (R^[J]) (R^[I,J]) := ⟨⟩
instance : TensorProductGetRXY R (R^[I]) (R^[J]) (R^[I,J]) := ⟨⟩


instance : TensorProductSelf R (R^[I]) (R^[I,I]) where

  identityMatrix :=
    let id : R^[I,I] := 0
    let data := BLAS.LevelOneDataExt.scaladd nI 1 id.data 0 (nI+1) 1
    ⟨data, sorry_proof⟩

  identityMatrix_spec := sorry_proof

  addIdentityMatrix a A :=
    let data := BLAS.LevelOneDataExt.scaladd nI 1 A.data 0 (nI+1) a
    ⟨data, sorry_proof⟩

  addIdentityMatrix_spec := sorry_proof



variable (A : R^[10,20]) (B : R^[20,5]) (x : R^[5])

/-- info: A * B * x : R^[10] -/
#guard_msgs in
#check A*B*x
