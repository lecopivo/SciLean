import LeanBLAS
import SciLean.Data.DataArray.DataArray
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



open Function in
/-- `HasRnEquiv X n R` says that `X` is canonically isomorphic to `R^[n]`

This provides class provides:
  - `toRn : X → R^[n]`
  - `fromRn : R^[n] → X`

This class is supposed to be zero cost at runtime or close to zero.
-/
class HasRnEquiv (X : Type*) (n : outParam ℕ) (R : outParam Type*)
    [RealScalar R] [PlainDataType R] where
  toRn : X → R^[n]
  fromRn : R^[n] → X
  protected left_inv : LeftInverse fromRn toRn
  protected right_inv : RightInverse fromRn toRn


export HasRnEquiv (toRn fromRn)

section Simps

variable (X : Type*) {n : ℕ}
  {R : Type*} [RealScalar R] [PlainDataType R] [HasRnEquiv X n R]

@[simp, simp_core]
theorem toRn_fromRn (x : R^[n]) : toRn (fromRn x : X) = x := HasRnEquiv.right_inv _

@[simp, simp_core]
theorem fromRn_toRn (x : X) : fromRn (toRn x) = x := HasRnEquiv.left_inv _

end Simps


instance {R : Type*} [RealScalar R] [PlainDataType R] :
    HasRnEquiv R 1 R where
  toRn x := ⊞[x]
  fromRn x := x[0]
  left_inv := by intro x; simp
  right_inv := by sorry_proof

instance {X R : Type*} [RealScalar R] [PlainDataType R]
    [HasRnEquiv X n R] [PlainDataType X]
    {I nI} [IdxType I nI] :
    HasRnEquiv (X^[I]) (nI*n) R where
  toRn x := cast sorry_proof x
  fromRn x := cast sorry_proof x
  left_inv := by sorry_proof
  right_inv := by sorry_proof


section Operations

variable (X : Type*) {n : ℕ}
  {R : Type*} [RealScalar R] [PlainDataType R] [HasRnEquiv X n R]
  [BLAS (DataArray R) R R]

@[inline]
def _root_.Add.ofRnEquiv : Add X := ⟨fun x y =>
  let data := BLAS.LevelOneData.axpy n 1 (toRn x).1 0 1 (toRn y).1 0 1
  fromRn (⟨data,sorry_proof⟩ : R^[n])⟩

@[inline]
def _root_.Sub.ofRnEquiv : Sub X := ⟨fun x y =>
  let data := BLAS.LevelOneDataExt.axpby n 1 (toRn x).1 0 1 (-1) (toRn y).1 0 1
  fromRn (⟨data,sorry_proof⟩ : R^[n])⟩

@[inline]
def _root_.Neg.ofRnEquiv : Neg X := ⟨fun x =>
  let data := BLAS.LevelOneData.scal n (-1) (toRn x).1 0 1
  fromRn (⟨data,sorry_proof⟩ : R^[n])⟩

@[inline]
def _root_.SMul.ofRnEquiv : SMul R X := ⟨fun r x =>
  let data := BLAS.LevelOneData.scal n r (toRn x).1 0 1
  fromRn (⟨data,sorry_proof⟩ : R^[n])⟩

@[inline]
def _root_.Zero.ofRnEquiv : Zero X := ⟨
  let data := BLAS.LevelOneDataExt.const n (0:R)
  fromRn (⟨data,sorry_proof⟩ : R^[n])⟩

@[inline]
def _root_.Inner.ofRnEquiv : Inner R X := ⟨fun x y =>
  BLAS.LevelOneData.dot n (toRn x).1 0 1 (toRn y).1 0 1⟩

@[inline]
def _root_.NSMul.ofRnEquiv : SMul ℕ X := ⟨fun m x =>
  let data := BLAS.LevelOneData.scal n (m:R) (toRn x).1 0 1
  fromRn (⟨data,sorry_proof⟩ : R^[n])⟩

@[inline]
def _root_.ZSMul.ofRnEquiv : SMul ℤ X := ⟨fun z x =>
  let data := BLAS.LevelOneData.scal n (z:R) (toRn x).1 0 1
  fromRn (⟨data,sorry_proof⟩ : R^[n])⟩

@[inline]
def _root_.Norm.ofRnEquiv : Norm X := ⟨fun x =>
  let norm := BLAS.LevelOneData.nrm2 n (toRn x).1 0 1
  Scalar.toReal R norm⟩

end Operations


section Algebra

variable (X : Type*) {n : ℕ}
  {R : Type*} [RealScalar R] [PlainDataType R] [HasRnEquiv X n R]
  [BLAS (DataArray R) R R] [LawfulBLAS (DataArray R) R R]


/-- Transfers `AddCommGroup` structure from `R^[n]` to `X` together with all operations. -/
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




/-- Equivalence with `R^[n]` is consistent with getting elements. -/
class IsRnEquivGetElem (X I R : Type*)
    {nI} [IdxType I nI] [RealScalar R] [PlainDataType R] [HasRnEquiv X nI R]
    [GetElem' X I R] : Prop where
  getElem_eq_toRn_getElem (x : X) (i : I) :
    x[i] = (toRn x)[toIdx i]

/-- Equivalence with `R^[n]` is consistent with settting elements. -/
class IsRnEquivSetElem (X I R : Type*)
    {nI} [IdxType I nI] [RealScalar R] [PlainDataType R] [HasRnEquiv X nI R]
    [SetElem' X I R] : Prop where
  setElem_eq_toRn_setElem (x : X) (i : I) (v : R) :
    setElem x i v .intro = fromRn (setElem (toRn x) (toIdx i) v .intro)
