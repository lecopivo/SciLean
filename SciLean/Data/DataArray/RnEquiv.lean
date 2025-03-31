import LeanBLAS
import SciLean.Data.DataArray.DataArray
import SciLean.Data.DataArray.DataArrayEquiv
import SciLean.Analysis.Scalar.Basic
import SciLean.Analysis.AdjointSpace.Basic

/-! Class `HasRnEquiv X n R` states that `X` is canonically isomorphic to `R^[n]`

Main functions:
  - `toRn : X → R^[n]`
  - `fromRn : R^[n] → X`

Functions to transfer structures from `R^[n]` to `X`
  - `<class>.ofRnEquiv` - transfers corresponding class from `R^[n]` to `X`
-/

namespace SciLean

namespace DataArrayN


instance instHasRnEquivInductive
    {R : Type*} [RealScalar R] [PlainDataType R]
    {I nI} [IndexType I nI] {J nJ} [IndexType J nJ]
    {X : Type*} [HasRnEquiv X J R] [PlainDataType X] :
    HasRnEquiv (X^[I]) (I × J) R where

-- instance instHasRnEquivBase
--     {R : Type*} [RealScalar R] [PlainDataType R]
--     {I nI} [IndexType I nI] :
--     HasRnEquiv (R^[I]) I R where

instance instHasRnEquivSelf
    {R : Type*} [RealScalar R] [PlainDataType R] :
    HasRnEquiv R Unit R where


-- I'm unsure if we really want these instances or operations like this should be done
-- through `toRn` and `fromRn`
section RGetSet

variable {X : Type*} [PlainDataType X]
  {I : Type*} {nI : ℕ} [IndexType I nI] {J : Type*} {nJ : ℕ} [IndexType J nJ]
  {R : Type*} [RealScalar R] [PlainDataType R]
  [HasRnEquiv X J R]

instance : GetElem' (X^[I]) (Idx (nI*nJ)) R where
  getElem x i _ := (toRn x).linGet i

instance : InjectiveGetElem (X^[I]) (Idx (nI*nJ)) where
  getElem_injective := sorry_proof

instance : SetElem' (X^[I]) (Idx (nI*nJ)) R where
  setElem x i v _ := fromRn ((toRn x).linSet i v)
  setElem_valid := sorry_proof

instance : LawfulSetElem (X^[I]) (Idx (nI*nJ)) where
  getElem_setElem_eq := sorry_proof
  getElem_setElem_neq := sorry_proof

instance : OfFn (X^[I]) (Idx (nI*nJ)) R where
  ofFn f := fromRn ((ofFn f : R^[nI*nJ]).reshape (I×J) sorry_proof)

instance : LawfulOfFn (X^[I]) (Idx (nI*nJ)) where
  getElem_ofFn := sorry_proof

abbrev rget (x : X^[I]) (i : Idx (nI*nJ)) : R := x[i]
abbrev rset (x : X^[I]) (i : Idx (nI*nJ)) (v : R) : X^[I] := setElem x i v .intro

section Operations

variable (X : Type*)
  {I : Type*} {nI : ℕ} [IndexType I nI]
  {R : Type*} [RealScalar R] [PlainDataType R] [BLAS (DataArray R) R R]
  [HasRnEquiv X I R]


@[inline]
def _root_.Add.ofRnEquiv : Add X := ⟨fun x y =>
  let data := BLAS.LevelOneData.axpy nI 1 (toRn x).1 0 1 (toRn y).1 0 1
  fromRn (⟨data,sorry_proof⟩ : R^[I])⟩

@[inline]
def _root_.Sub.ofRnEquiv : Sub X := ⟨fun x y =>
  let data := BLAS.LevelOneDataExt.axpby nI 1 (toRn x).1 0 1 (-1) (toRn y).1 0 1
  fromRn (⟨data,sorry_proof⟩ : R^[I])⟩

@[inline]
def _root_.Neg.ofRnEquiv : Neg X := ⟨fun x =>
  let data := BLAS.LevelOneData.scal nI (-1) (toRn x).1 0 1
  fromRn (⟨data,sorry_proof⟩ : R^[I])⟩

@[inline]
def _root_.SMul.ofRnEquiv : SMul R X := ⟨fun r x =>
  let data := BLAS.LevelOneData.scal nI r (toRn x).1 0 1
  fromRn (⟨data,sorry_proof⟩ : R^[I])⟩

@[inline]
def _root_.Zero.ofRnEquiv : Zero X := ⟨
  let data := BLAS.LevelOneDataExt.const nI (0:R)
  fromRn (⟨data,sorry_proof⟩ : R^[I])⟩

@[inline]
def _root_.Inner.ofRnEquiv : Inner R X := ⟨fun x y =>
  BLAS.LevelOneData.dot nI (toRn x).1 0 1 (toRn y).1 0 1⟩

@[inline]
def _root_.NSMul.ofRnEquiv : SMul ℕ X := ⟨fun m x =>
  let data := BLAS.LevelOneData.scal nI (m:R) (toRn x).1 0 1
  fromRn (⟨data,sorry_proof⟩ : R^[I])⟩

@[inline]
def _root_.ZSMul.ofRnEquiv : SMul ℤ X := ⟨fun z x =>
  let data := BLAS.LevelOneData.scal nI (z:R) (toRn x).1 0 1
  fromRn (⟨data,sorry_proof⟩ : R^[I])⟩

@[inline]
def _root_.Norm.ofRnEquiv : Norm X := ⟨fun x =>
  let norm := BLAS.LevelOneData.nrm2 nI (toRn x).1 0 1
  Scalar.toReal R norm⟩

end Operations


section Algebra

variable (X : Type*)
  {I : Type*} {nI : ℕ} [IndexType I nI]
  {R : Type*} [RealScalar R] [PlainDataType R] [BLAS (DataArray R) R R]
  [HasRnEquiv X I R]


/-- Transfers `AddCommGroup` structure from `R^[I]` to `X` together with all operations. -/
@[inline]
def _root_.NormedAddCommGroup.ofRnEquiv : NormedAddCommGroup X := {
  toAdd := Add.ofRnEquiv X
  toSub := Sub.ofRnEquiv X
  toNeg := Neg.ofRnEquiv X
  toZero := Zero.ofRnEquiv X

  add_assoc := sorry_proof
  zero_add := sorry_proof
  add_zero := sorry_proof
  nsmul := (NSMul.ofRnEquiv X).1
  nsmul_zero := sorry_proof
  nsmul_succ := sorry_proof
  zsmul := (ZSMul.ofRnEquiv X).1
  zsmul_zero' := sorry_proof
  zsmul_succ' := sorry_proof
  zsmul_neg' := sorry_proof
  neg_add_cancel := sorry_proof
  add_comm := sorry_proof
  sub_eq_add_neg := sorry_proof

  toNorm := Norm.ofRnEquiv X
  dist_self := sorry_proof
  dist_comm := sorry_proof
  dist_triangle := sorry_proof
  eq_of_dist_eq_zero := sorry_proof
}

@[inline]
def _root_.AdjointSpace.ofRnEquiv [NormedAddCommGroup X] : AdjointSpace R X := {
  toSMul := SMul.ofRnEquiv X
  toInner := Inner.ofRnEquiv X
  one_smul := sorry_proof
  mul_smul := sorry_proof
  smul_zero := sorry_proof
  smul_add := sorry_proof
  add_smul := sorry_proof
  zero_smul := sorry_proof
  norm_smul_le := sorry_proof
  inner_top_equiv_norm := sorry_proof
  conj_symm := sorry_proof
  add_left := sorry_proof
  smul_left := sorry_proof
}


end Algebra
