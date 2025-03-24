import SciLean.Data.DataArray.DataArrayEquiv
import SciLean.Data.VectorType.Base

import LeanBLAS

namespace SciLean

open BLAS


----------------------------------------------------------------------------------------------------
-- VectorType instances ----------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


open IndexType in
instance
    {nI} [IndexType I nI] {nJ} [IndexType J nJ]
    {R : Type*} [RealScalar R] [PlainDataType R] [BLAS (DataArray R) R R]
    {X : Type*} [PlainDataType X] [HasRnEquiv (X^[J]) I R]
    [GetElem' (X^[J]) I R] :
    VectorType.Base (X^[J]) I R where
  zero :=
    let N := nI
    let x' : DataArray R := BLAS.LevelOneDataExt.const N (0:R)
    fromRn ⟨x', sorry_proof⟩
  zero_spec := sorry_proof
  scal a x :=
    let N := nI
    let xptr := (toRn x).1
    let x' := BLAS.LevelOneData.scal N a xptr 0 1
    fromRn ⟨x', sorry_proof⟩
  scal_spec := sorry_proof
  sum x :=
    let N := nI
    let xptr := (toRn x).1
    let s := BLAS.LevelOneDataExt.sum N xptr 0 1
    s
  sum_spec := sorry_proof
  asum x :=
    let N := nI
    let xptr := (toRn x).1
    let s := BLAS.LevelOneData.asum N xptr 0 1
    s
  asum_spec := sorry_proof
  nrm2 x :=
    let N := nI
    let xptr := (toRn x).1
    let s := BLAS.LevelOneData.nrm2 N xptr 0 1
    s
  nrm2_spec := sorry_proof
  iamax x _ :=
    let N := nI
    let xptr := (toRn x).1
    let idx := (BLAS.LevelOneData.iamax N xptr 0 1).toUSize
    fromIdx ⟨idx, sorry_proof⟩
  iamax_spec := sorry_proof
  imaxRe x _ :=
    let N := nI
    let xptr := (toRn x).1
    let idx := (BLAS.LevelOneDataExt.imaxRe N xptr 0 1 sorry_proof).toUSize
    fromIdx ⟨idx, sorry_proof⟩
  imaxRe_spec := sorry_proof
  iminRe x _ :=
    let N := nI
    let xptr := (toRn x).1
    let idx := (BLAS.LevelOneDataExt.iminRe N xptr 0 1 sorry_proof).toUSize
    fromIdx ⟨idx, sorry_proof⟩
  iminRe_spec := sorry_proof
  dot x y :=
    let N := nI
    let xptr := (toRn x).1
    let yptr := (toRn y).1
    let s := BLAS.LevelOneData.dot N xptr 0 1 yptr 0 1
    s
  dot_spec := sorry_proof
  conj x :=
    let _ : Nat := panic! "conj not impolemented for X with ScalarArrayEquiv"
    x
  conj_spec := sorry_proof
  axpy a x y :=
    let N := nI
    let xptr := (toRn x).1
    let yptr := (toRn y).1
    let y' := BLAS.LevelOneData.axpy N a xptr 0 1 yptr 0 1
    fromRn ⟨y', sorry_proof⟩
  axpy_spec := sorry_proof
  axpby a x b y :=
    let N := nI
    let xptr := (toRn x).1
    let yptr := (toRn y).1
    let y' := BLAS.LevelOneDataExt.axpby N a xptr 0 1 b yptr 0 1
    fromRn ⟨y', sorry_proof⟩
  axpby_spec := sorry_proof
  mul x y :=
    let N := nI
    let xptr := (toRn x).1
    let yptr := (toRn y).1
    let y' := BLAS.LevelOneDataExt.mul N xptr 0 1 yptr 0 1
    fromRn ⟨y', sorry_proof⟩
  mul_spec := sorry_proof

-- #exit

-- instance {X I R K : Type*}
--     {nI} [IndexType I nI] [PlainDataType K]
--     [DefaultDataArrayEquiv X I K] [GetElem' X I K]
--     [RealScalar R] [Scalar R K]
--     [BLAS (DataArray K) R K] [LawfulBLAS (DataArray K) R K]
--     [SetElem' X I K] [LawfulSetElem X I]
--     [OfFn X I K] [LawfulOfFn X I] [Fold I] :
--     VectorType.Dense X where
--   fromVec f :=
--     let x := DataArray.intro fun i => f i
--     fromRn _ (I:=I) ⟨x, sorry_proof⟩
--   right_inv := sorry_proof
--   -- set_spec := sorry_proof
--   const v :=
--     let x := BLAS.LevelOneDataExt.const (nI) v
--     fromRn _ (I:=I) (K:=K) ⟨x, sorry_proof⟩
--   const_spec := sorry_proof
--   scalAdd a b x :=
--     let N := nI
--     let x := toRn I K x
--     let x := BLAS.LevelOneDataExt.scaladd N a x.1 0 1 b
--     fromRn _ (I:=I) ⟨x, sorry_proof⟩
--   scalAdd_spec := sorry_proof
--   div x y :=
--     let N := nI
--     let x := toRn I K x
--     let y := toRn I K y
--     let x := BLAS.LevelOneDataExt.div N x.1 0 1 y.1 0 1
--     fromRn _ (I:=I) ⟨x, sorry_proof⟩
--   div_spec := sorry_proof
--   inv x :=
--     let N := nI
--     let x := toRn I K x
--     let x := BLAS.LevelOneDataExt.inv N x.1 0 1
--     fromRn _ (I:=I) ⟨x, sorry_proof⟩
--   inv_spec := sorry_proof
--   exp x :=
--     let N := nI
--     let x := toRn I K x
--     let x := BLAS.LevelOneDataExt.exp N x.1 0 1
--     fromRn _ (I:=I) ⟨x, sorry_proof⟩
--   exp_spec := sorry_proof
