import LeanBLAS

import SciLean.Data.DataArray.DataArray
import SciLean.Data.FloatArray
import SciLean.Analysis.Scalar.FloatAsReal

namespace SciLean

open BLAS CBLAS

local instance : Coe (DataArray Float) Float64Array := ⟨fun x => cast sorry_proof x⟩
local instance : Coe (Float64Array) (DataArray Float) := ⟨fun x => cast sorry_proof x⟩

instance : LevelOneData (DataArray Float) Float Float where
  size x := x.size
  get x i := if i < x.size then x.get ⟨i.toUSize,sorry_proof⟩ else 0
  dot N X offX incX Y offY incY := ddot N.toUSize X offX.toUSize incX.toUSize Y offY.toUSize incY.toUSize
  nrm2 N X offX incX := dnrm2 N.toUSize X offX.toUSize incX.toUSize
  asum N X offX incX := dasum N.toUSize X offX.toUSize incX.toUSize
  iamax N X offX incX := idamax N.toUSize X offX.toUSize incX.toUSize |>.toNat
  swap N X offX incX Y offY incY :=
    let (x,y) := dswap N.toUSize X offX.toUSize incX.toUSize Y offY.toUSize incY.toUSize
    (x,y)
  copy N X offX incX Y offY incY := dcopy N.toUSize X offX.toUSize incX.toUSize Y offY.toUSize incY.toUSize
  axpy N a X offX incX Y offY incY := daxpy N.toUSize a X offX.toUSize incX.toUSize Y offY.toUSize incY.toUSize
  rotg a b := drotg a b
  rotmg d1 d2 b1 b2 := drotmg d1 d2 b1 b2
  rot N X offX incX Y offY incY c s :=
    let (x,y) := drot N.toUSize X offX.toUSize incX.toUSize Y offY.toUSize incY.toUSize c s
    (x,y)
  scal N a X offX incX := dscal N.toUSize a X offX.toUSize incX.toUSize

set_option linter.unusedVariables false in
instance : LevelOneDataExt (DataArray Float) Float Float where
  const N a := dconst N.toUSize a
  sum N X offX incX := dsum N.toUSize X offX.toUSize incX.toUSize
  axpby N a X offX incX b Y offY incY := daxpby N.toUSize a X offX.toUSize incX.toUSize b Y offY.toUSize incY.toUSize
  scaladd N a X offX incX b := dscaladd N.toUSize a X offX.toUSize incX.toUSize b

  imaxRe N X offX incX h := (dimaxRe N.toUSize X offX.toUSize incX.toUSize).toNat
  imaxIm N X offX incX h := offX
  iminRe N X offX incX h := (diminRe N.toUSize X offX.toUSize incX.toUSize).toNat
  iminIm N X offX incX h := offX

  mul N X offX incX Y offY incY := dmul N.toUSize X offX.toUSize incX.toUSize Y offY.toUSize incY.toUSize
  div N X offX incX Y offY incY := ddiv N.toUSize X offX.toUSize incX.toUSize Y offY.toUSize incY.toUSize
  inv N X offX incX := dinv N.toUSize X offX.toUSize incX.toUSize
  abs N X offX incX := dabs N.toUSize X offX.toUSize incX.toUSize
  sqrt N X offX incX := dsqrt N.toUSize X offX.toUSize incX.toUSize
  exp N X offX incX := dexp N.toUSize X offX.toUSize incX.toUSize
  log N X offX incX := dlog N.toUSize X offX.toUSize incX.toUSize
  sin N X offX incX := dsin N.toUSize X offX.toUSize incX.toUSize
  cos N X offX incX := dcos N.toUSize X offX.toUSize incX.toUSize


instance : LevelTwoData (DataArray Float) Float Float where

  gemv order trans M N a A offA ldaA X offX incX b Y offY incY :=
    dgemv order trans M.toUSize N.toUSize a
      A offA.toUSize ldaA.toUSize X offX.toUSize incX.toUSize b Y offY.toUSize incY.toUSize

  bmv order trans M N KL KU a A offA ldaA X offX incX b Y offY incY :=
    dbmv order trans M.toUSize N.toUSize KL.toUSize KU.toUSize a
      A offA.toUSize ldaA.toUSize X offX.toUSize incX.toUSize b Y offY.toUSize incY.toUSize

  trmv order uplo trans diag N A offA lda X offX incX :=
    dtrmv order uplo trans diag N.toUSize A offA.toUSize lda.toUSize X offX.toUSize incX.toUSize

  tbmv order uplo trans diag N K A offA lda X offX incX :=
    dtbmv order uplo trans diag N.toUSize K.toUSize A offA.toUSize lda.toUSize X offX.toUSize incX.toUSize

  tpmv order uplo trans diag N A offA X offX incX :=
    dtpmv order uplo trans diag N.toUSize A offA.toUSize X offX.toUSize incX.toUSize

  trsv order uplo trans diag N A offA lda X offX incX :=
    dtrsv order uplo trans diag N.toUSize A offA.toUSize lda.toUSize X offX.toUSize incX.toUSize

  tbsv order uplo trans diag N K A offA lda X offX incX :=
    dtbsv order uplo trans diag N.toUSize K.toUSize A offA.toUSize lda.toUSize X offX.toUSize incX.toUSize

  tpsv order uplo trans diag N A offA X offX incX :=
    dtpsv order uplo trans diag N.toUSize A offA.toUSize X offX.toUSize incX.toUSize

  ger order M N a X offX incX Y offY incY A offA lda :=
    dger order M.toUSize N.toUSize a X offX.toUSize incX.toUSize Y offY.toUSize incY.toUSize A offA.toUSize lda.toUSize

  her order uplo N alpha X offX incX A offA lda :=
    dsyr order uplo N.toUSize alpha X offX.toUSize incX.toUSize A offA.toUSize lda.toUSize

  her2 order uplo N alpha X offX incX Y offY incY A offA lda :=
    dsyr2 order uplo N.toUSize alpha X offX.toUSize incX.toUSize Y offY.toUSize incY.toUSize A offA.toUSize lda.toUSize


instance : BLAS (DataArray Float) Float Float where

-- This is provable under the assumption `RCLike Float`
instance : LawfulBLAS (DataArray Float) Float Float := sorry_proof
