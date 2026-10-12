module

public import LeanBLAS
public import SciLean.Data.DataArray.DataArray
public import SciLean.Data.DataArray.DataArrayEquiv
public import SciLean.Analysis.Scalar.Basic
public import SciLean.Analysis.AdjointSpace.Basic

@[expose] public section


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
  -- linear indices are exactly the indices `toIdx (i,j)`, so this follows from the injectivity
  -- of the element access on `R^[I×J]` and the injectivity of `toRn`
  getElem_injective := by
    intro x y h
    have h' : ∀ i : Idx (nI*nJ), (toRn x).linGet i = (toRn y).linGet i := fun i => congrFun h i
    have hxy : toRn (I:=I×J) x = toRn y := by
      apply InjectiveGetElem.getElem_injective (idx := I×J)
      funext i
      exact h' (toIdx i)
    have h2 := congrArg (fromRn (X := X^[I])) hxy
    exact (DataArrayEquiv.left_inv x).symm.trans (h2.trans (DataArrayEquiv.left_inv y))

instance : SetElem' (X^[I]) (Idx (nI*nJ)) R where
  setElem x i v _ := fromRn ((toRn x).linSet i v)
  setElem_valid := by rfl

instance : LawfulSetElem (X^[I]) (Idx (nI*nJ)) where
  -- `toRn` undoes `fromRn` and then this is the `fromByteArray_toByteArray` law
  getElem_setElem_eq := by
    intro x i v _
    show (toRn (fromRn (X := X^[I]) ((toRn x).linSet i v))).linGet i = v
    rw [show (toRn (fromRn (X := X^[I]) ((toRn x).linSet i v))) = (toRn x).linSet i v from
      DataArrayEquiv.right_inv _]
    exact PlainDataType.btype.fromByteArray_toByteArray v _ _ _ _
  -- as above, then this is the law of `R^[I×J]` at the indices `fromIdx i`, `fromIdx j`
  getElem_setElem_neq := by
    intro x i j v _ _ hij
    show (toRn (fromRn (X := X^[I]) ((toRn x).linSet i v))).linGet j = (toRn x).linGet j
    rw [show (toRn (fromRn (X := X^[I]) ((toRn x).linSet i v))) = (toRn x).linSet i v from
      DataArrayEquiv.right_inv _]
    have h := getElem_setElem_neq (toRn x) (fromIdx i : I×J) (fromIdx j) v .intro .intro
      (fun h => hij (by simpa using congrArg toIdx h))
    change ((toRn x).linSet (toIdx (fromIdx i : I×J)) v).linGet (toIdx (fromIdx j : I×J))
      = (toRn x).linGet (toIdx (fromIdx j : I×J)) at h
    rwa [IndexType.toIdx_fromIdx, IndexType.toIdx_fromIdx] at h

instance : OfFn (X^[I]) (Idx (nI*nJ)) R where
  ofFn f := fromRn ((ofFn f : R^[nI*nJ]).reshape (I×J) (by rfl))

instance : LawfulOfFn (X^[I]) (Idx (nI*nJ)) where
  -- `toRn` undoes `fromRn` and then this is the law of `R^[nI*nJ]`
  getElem_ofFn := by
    intro f i
    show (toRn (fromRn (X := X^[I]) ((ofFn f : R^[nI*nJ]).reshape (I×J) (by rfl)))).linGet i = f i
    rw [show toRn (fromRn (X := X^[I]) ((ofFn f : R^[nI*nJ]).reshape (I×J) (by rfl)))
      = (ofFn f : R^[nI*nJ]).reshape (I×J) (by rfl) from DataArrayEquiv.right_inv _]
    exact getElem_ofFn (coll := R^[nI*nJ]) f i

abbrev rget (x : X^[I]) (i : Idx (nI*nJ)) : R := x[i]
abbrev rset (x : X^[I]) (i : Idx (nI*nJ)) (v : R) : X^[I] := setElem x i v .intro

section Operations

variable (X : Type*)
  {I : Type*} {nI : ℕ} [IndexType I nI]
  {R : Type*} [RealScalar R] [PlainDataType R] [BLAS (DataArray R) R R]
  [HasRnEquiv X I R]


@[instance_reducible, inline]
def _root_.Add.ofRnEquiv : Add X := ⟨fun x y =>
  let data := BLAS.LevelOneData.axpy nI 1 (toRn x).1 0 1 (toRn y).1 0 1
  fromRn (⟨data,sorry_proof⟩ : R^[I])⟩

@[instance_reducible, inline]
def _root_.Sub.ofRnEquiv : Sub X := ⟨fun x y =>
  let data := BLAS.LevelOneDataExt.axpby nI 1 (toRn x).1 0 1 (-1) (toRn y).1 0 1
  fromRn (⟨data,sorry_proof⟩ : R^[I])⟩

@[instance_reducible, inline]
def _root_.Neg.ofRnEquiv : Neg X := ⟨fun x =>
  let data := BLAS.LevelOneData.scal nI (-1) (toRn x).1 0 1
  fromRn (⟨data,sorry_proof⟩ : R^[I])⟩

@[instance_reducible, inline]
def _root_.SMul.ofRnEquiv : SMul R X := ⟨fun r x =>
  let data := BLAS.LevelOneData.scal nI r (toRn x).1 0 1
  fromRn (⟨data,sorry_proof⟩ : R^[I])⟩

@[instance_reducible, inline]
def _root_.Zero.ofRnEquiv : Zero X := ⟨
  let data := BLAS.LevelOneDataExt.const nI (0:R)
  fromRn (⟨data,sorry_proof⟩ : R^[I])⟩

@[instance_reducible, inline]
def _root_.Inner.ofRnEquiv : Inner R X := ⟨fun x y =>
  BLAS.LevelOneData.dot nI (toRn x).1 0 1 (toRn y).1 0 1⟩

@[instance_reducible, inline]
def _root_.NSMul.ofRnEquiv : SMul ℕ X := ⟨fun m x =>
  let data := BLAS.LevelOneData.scal nI (m:R) (toRn x).1 0 1
  fromRn (⟨data,sorry_proof⟩ : R^[I])⟩

@[instance_reducible, inline]
def _root_.ZSMul.ofRnEquiv : SMul ℤ X := ⟨fun z x =>
  let data := BLAS.LevelOneData.scal nI (z:R) (toRn x).1 0 1
  fromRn (⟨data,sorry_proof⟩ : R^[I])⟩

@[instance_reducible, inline]
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
@[instance_reducible, inline]
def _root_.NormedAddCommGroup.ofRnEquiv : NormedAddCommGroup X :=
  letI := Add.ofRnEquiv X
  letI := Zero.ofRnEquiv X
  have zero_add : ∀ x : X, 0 + x = x := sorry_proof
  have add_comm : ∀ x y : X, x + y = y + x := sorry_proof
  have nsmul_zero : ∀ x : X, (NSMul.ofRnEquiv X).1 0 x = 0 := sorry_proof
  have nsmul_succ : ∀ (n : ℕ) (x : X),
      (NSMul.ofRnEquiv X).1 (n + 1) x = (NSMul.ofRnEquiv X).1 n x + x := sorry_proof
  {
  toAdd := Add.ofRnEquiv X
  toSub := Sub.ofRnEquiv X
  toNeg := Neg.ofRnEquiv X
  toZero := Zero.ofRnEquiv X

  add_assoc := sorry_proof
  zero_add := zero_add
  add_zero := fun x => (add_comm x 0).trans (zero_add x)
  nsmul := (NSMul.ofRnEquiv X).1
  nsmul_zero := nsmul_zero
  nsmul_succ := nsmul_succ
  zsmul := (ZSMul.ofRnEquiv X).1
  zsmul_zero' := fun x => by
    have h := nsmul_zero x
    change fromRn (⟨BLAS.LevelOneData.scal nI ((0:ℕ):R) (toRn x).1 0 1, _⟩ : R^[I]) = 0 at h
    change fromRn (⟨BLAS.LevelOneData.scal nI ((0:ℤ):R) (toRn x).1 0 1, _⟩ : R^[I]) = 0
    simp only [Nat.cast_zero] at h; simpa only [Int.cast_zero] using h
  zsmul_succ' := fun n x => by
    have h := nsmul_succ n x
    change fromRn (⟨BLAS.LevelOneData.scal nI ((n+1:ℕ):R) (toRn x).1 0 1, _⟩ : R^[I])
      = fromRn (⟨BLAS.LevelOneData.scal nI ((n:ℕ):R) (toRn x).1 0 1, _⟩ : R^[I]) + x at h
    change fromRn (⟨BLAS.LevelOneData.scal nI ((n.succ:ℤ):R) (toRn x).1 0 1, _⟩ : R^[I])
      = fromRn (⟨BLAS.LevelOneData.scal nI ((n:ℤ):R) (toRn x).1 0 1, _⟩ : R^[I]) + x
    simpa only [Int.cast_natCast, Nat.succ_eq_add_one] using h
  zsmul_neg' := sorry_proof
  neg_add_cancel := sorry_proof
  add_comm := add_comm
  sub_eq_add_neg := sorry_proof

  toNorm := Norm.ofRnEquiv X
  dist_self := sorry_proof
  dist_comm := sorry_proof
  dist_triangle := sorry_proof
  eq_of_dist_eq_zero := sorry_proof
}

@[instance_reducible, inline]
def _root_.AdjointSpace.ofRnEquiv [NormedAddCommGroup X] : AdjointSpace R X :=
  letI := SMul.ofRnEquiv (R:=R) X
  have smul_add : ∀ (r : R) (x y : X), r • (x + y) = r • x + r • y := sorry_proof
  have add_smul : ∀ (r s : R) (x : X), (r + s) • x = r • x + s • x := sorry_proof
  {
  toSMul := SMul.ofRnEquiv X
  toInner := Inner.ofRnEquiv X
  one_smul := sorry_proof
  mul_smul := sorry_proof
  smul_zero := fun r => by
    have h := smul_add r 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  smul_add := smul_add
  add_smul := add_smul
  zero_smul := fun x => by
    have h := add_smul 0 0 x
    rw [add_zero] at h
    exact left_eq_add.mp h
  norm_smul_le := sorry_proof
  inner_top_equiv_norm := sorry_proof
  conj_symm := sorry_proof
  add_left := sorry_proof
  smul_left := sorry_proof
}


end Algebra
