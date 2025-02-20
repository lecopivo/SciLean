import SciLean.Data.DataArray.ScalarArray
import SciLean.Data.VectorType.Base
import SciLean.Data.MatrixType.Base
import SciLean.Data.MatrixType.Dense
import SciLean.Data.MatrixType.Square

namespace SciLean


open IndexType in
/-- This instance says that `X` is equivalent to an array of `size I` scalars `K` and it will
automatically provide vector space structure on `X` through this equivalence.

It is expected that this equivalence is cheap at runtime like casting `ByteArray` to `FloatArray`.

The index type `I` is the canonical type to index scalar compotents of `X`.

The type parameter `R` represents the type of reals associated with scalar `K` which is expected
to model eiter complex or real numbers. When `K` models real numbers then `R` is the same as `K`. -/
class ScalarArrayEquiv (X : Type*) (Array I R K : outParam Type*)
    [BLAS Array R K] [IndexType I] [GetElem X I K (fun _ _ => True)] where
  /-- Array of `X` as byte array (this is `DataArray X`) can be converted to an array of scalars
  that has `m*(size I)` elements for appropriate `I`. -/
  equiv : X ≃ { a : Array // BLAS.LevelOneData.size a = size I }
  getElem_equiv : ∀ (x : X) (i : I), BLAS.LevelOneData.get (equiv x).1 (toFin i).1 = x[i]

namespace ScalarArrayEquiv

section Simps
variable (X : Type*) (Array I R K : outParam Type*)
  [GetElem X I K (fun _ _ => True)] [IndexType I] [BLAS Array R K] [ScalarArrayEquiv X Array I R K]

@[simp]
theorem size_equiv (x : X) : BLAS.LevelOneData.size (equiv x).1 = size I := by sorry_proof

end Simps

-- this is a bad istance ...
-- we should have some `HasUncurry` for `DataArray` and use that!
-- instance {R X} [PlainDataType X] {I J} [IndexType I] [IndexType J]
--   [GetElem X J R (fun _ _ => True)] : GetElem (X^[I]) (I×J) R (fun _ _ => True) where
--   getElem x ij _ := x[ij.1][ij.2]

/-- `ScalarArray` implies `ScalarArrayEquiv` -/
instance {R Array I} [RealScalar R] [PlainDataType R] [ScalarArray R Array] [IndexType I] :
    ScalarArrayEquiv (R^[I]) Array I R R where
  equiv := {
    toFun x := ⟨ScalarArray.equiv x.1, by have h := x.2; simp_all⟩
    invFun a := ⟨ScalarArray.equiv.symm a.1, by have := a.2; simp_all⟩
    left_inv := by intro x; simp
    right_inv := by intro x; simp
  }
  getElem_equiv := sorry_proof

instance
  {R Array I} [RealScalar R] [PlainDataType R] [ScalarArray R Array] [IndexType I] [IndexType J] :
    ScalarArrayEquiv (R^[J]^[I]) Array (I×J) R R where
  equiv := {
    -- X^[I] --> R^[I×J] --> Array
    toFun x :=
      let x : DataArray R :=
        ⟨x.1.1, size I * size J,
         by have := x.2; have := x.1.3;
            /- we need some coherency between `PlainDataType R` and `PlainDataType X` -/
            sorry_proof⟩
      ⟨ScalarArray.equiv x, sorry_proof⟩
    invFun a :=
      let a : DataArray R := ScalarArray.equiv.symm a.1
      ⟨⟨a.1, size I, sorry_proof⟩, by have := a.2; simp⟩
    left_inv := sorry_proof
    right_inv := sorry_proof
  }
  getElem_equiv := sorry_proof

section Operations

variable (X : Type*) (Array I R K : outParam Type*) [RealScalar R] [Scalar R K]
  [IndexType I] [BLAS Array R K] [GetElem X I K (fun _ _ => True)] [ScalarArrayEquiv X Array I R K]

open IndexType in
instance (X : Type*) (Array I R K : outParam Type*)
    {_ : RealScalar R} {_ : Scalar R K} {_ : BLAS Array R K} {_ : IndexType I}
    {_ : GetElem X I K (fun _ _ => True)}
    [e : ScalarArrayEquiv X Array I R K] [LawfulBLAS Array R K] :
    VectorType.Base X I K where
  zero :=
    let N := size I
    let x' := BLAS.LevelOneDataExt.const N 0
    e.equiv.symm ⟨x', sorry_proof⟩
  zero_spec := sorry_proof
  scal a x :=
    let N := size I
    let xptr := (e.equiv x).1
    let x' := BLAS.LevelOneData.scal N a xptr 0 1
    e.equiv.symm ⟨x', sorry_proof⟩
  scal_spec := by
    intro a x i
    simp[← ScalarArrayEquiv.getElem_equiv]
    rw[BLAS.LevelOneSpec.scal_spec, Nat.mod_one]
    · simp
    · intro i
      constructor <;> simp
    · simp[toFin]
  sum x :=
    let N := size I
    let xptr := (e.equiv x).1
    let s := BLAS.LevelOneDataExt.sum N xptr 0 1
    s
  sum_spec := sorry_proof
  asum x :=
    let N := size I
    let xptr := (e.equiv x).1
    let s := BLAS.LevelOneData.asum N xptr 0 1
    s
  asum_spec := sorry_proof
  nrm2 x :=
    let N := size I
    let xptr := (e.equiv x).1
    let s := BLAS.LevelOneData.nrm2 N xptr 0 1
    s
  nrm2_spec := sorry_proof
  iamax x :=
    let N := size I
    let xptr := (e.equiv x).1
    let idx := BLAS.LevelOneData.iamax N xptr 0 1
    fromFin ⟨idx, sorry_proof⟩
  iamax_spec := sorry_proof
  imaxRe x h :=
    let N := size I
    let xptr := (e.equiv x).1
    let idx := BLAS.LevelOneDataExt.imaxRe N xptr 0 1 sorry_proof
    fromFin ⟨idx, sorry_proof⟩
  imaxRe_spec := sorry_proof
  iminRe x h :=
    let N := size I
    let xptr := (e.equiv x).1
    let idx := BLAS.LevelOneDataExt.iminRe N xptr 0 1 sorry_proof
    fromFin ⟨idx, sorry_proof⟩
  iminRe_spec := sorry_proof
  dot x y :=
    let N := size I
    let xptr := (e.equiv x).1
    let yptr := (e.equiv y).1
    let s := BLAS.LevelOneData.dot N xptr 0 1 yptr 0 1
    s
  dot_spec := sorry_proof
  conj x :=
    let x' : Nat := panic! "conj not impolemented for X with ScalarArrayEquiv"
    x
  conj_spec := sorry_proof
  axpy a x y :=
    let N := size I
    let xptr := (e.equiv x).1
    let yptr := (e.equiv y).1
    let y' := BLAS.LevelOneData.axpy N a xptr 0 1 yptr 0 1
    e.equiv.symm ⟨y', sorry_proof⟩
  axpy_spec := sorry_proof
  axpby a x b y :=
    let N := size I
    let xptr := (e.equiv x).1
    let yptr := (e.equiv y).1
    let y' := BLAS.LevelOneDataExt.axpby N a xptr 0 1 b yptr 0 1
    e.equiv.symm ⟨y', sorry_proof⟩
  axpby_spec := sorry_proof
  mul x y :=
    let N := size I
    let xptr := (e.equiv x).1
    let yptr := (e.equiv y).1
    let y' := BLAS.LevelOneDataExt.mul N xptr 0 1 yptr 0 1
    e.equiv.symm ⟨y', sorry_proof⟩
  mul_spec := sorry_proof

-- instance (X : Type*) (Array I R K : outParam Type*)
--     {_ : RealScalar R} {_ : Scalar R K} {_ : BLAS Array R K} {_ : IndexType I}
--     {_ : GetElem X I K (fun _ _ => True)}
--     [e : ScalarArrayEquiv X Array I R K] [LawfulBLAS Array R K] :
--     LawfulGetElem X I where
--   getElem_injective := sorry_proof

-- open IndexType in
-- instance (X : Type*) (Array I R K : outParam Type*)
--     {_ : RealScalar R} {_ : Scalar R K} {_ : BLAS Array R K} {_ : IndexType I}
--     {_ : GetElem X I K (fun _ _ => True)}
--     [e : ScalarArrayEquiv X Array I R K] [LawfulBLAS Array R K] :
--     SetElem X I K (fun _ _ => True) where
--   setElem x i v _ :=
--     let x := e.equiv x
--     let x := BLAS.LevelOneData.set x.1 (toFin i) v
--     e.equiv.symm ⟨x, sorry_proof⟩
--   setElem_valid := sorry_proof

open IndexType in
instance (X : Type*) (Array I R K : outParam Type*)
    {_ : RealScalar R} {_ : Scalar R K} {_ : BLAS Array R K} {_ : IndexType I}
    {_ : GetElem X I K (fun _ _ => True)}
    [e : ScalarArrayEquiv X Array I R K] [LawfulBLAS Array R K]
    [SetElem X I K (fun _ _ => True)] [LawfulSetElem X I]
    [OfFn X I K] [LawfulOfFn X I] :
    VectorType.Dense X where
  fromVec f :=
    let x := BLAS.LevelOneData.ofFn (Array:=Array) (fun i => f (fromFin i))
    e.equiv.symm ⟨x, sorry_proof⟩
  right_inv := sorry_proof
  -- set_spec := sorry_proof
  const v :=
    let x := BLAS.LevelOneDataExt.const (size I) v
    e.equiv.symm ⟨x, sorry_proof⟩
  const_spec := sorry_proof
  scalAdd a b x :=
    let N := size I
    let x := e.equiv x
    let x := BLAS.LevelOneDataExt.scaladd N a x.1 0 1 b
    e.equiv.symm ⟨x, sorry_proof⟩
  scalAdd_spec := sorry_proof
  div x y :=
    let N := size I
    let x := e.equiv x
    let y := e.equiv y
    let x := BLAS.LevelOneDataExt.div N x.1 0 1 y.1 0 1
    e.equiv.symm ⟨x, sorry_proof⟩
  div_spec := sorry_proof
  inv x :=
    let N := size I
    let x := e.equiv x
    let x := BLAS.LevelOneDataExt.inv N x.1 0 1
    e.equiv.symm ⟨x, sorry_proof⟩
  inv_spec := sorry_proof
  exp x :=
    let N := size I
    let x := e.equiv x
    let x := BLAS.LevelOneDataExt.exp N x.1 0 1
    e.equiv.symm ⟨x, sorry_proof⟩
  exp_spec := sorry_proof


example (R m n : Type*) (Array : outParam Type*)
    [RealScalar R] [PlainDataType R] [IndexType m] [IndexType n]
    [ScalarArray R Array] [LawfulBLAS Array R R] :
    VectorType.Base (R^[m,n]) (m×n) R := by
  -- apply instBaseOfLawfulBLAS
  infer_instance

example (R m n : Type*) (Array : outParam Type*)
    [RealScalar R] [PlainDataType R] [IndexType m] [IndexType n]
    [ScalarArray R Array] [LawfulBLAS Array R R] :
    ScalarArrayEquiv (R^[m, n]) Array (m × n) R R := by
  apply instDataArrayN


instance (R m n : Type*) (Array : outParam Type*)
    [RealScalar R] [PlainDataType R] [IndexType m] [IndexType n]
    [e : ScalarArray R Array] [LawfulBLAS Array R R] :
    MatrixType.Base (R^[m,n]) (R^[n]) (R^[m]) where
  toMatrix A i j := A[i,j]
  toVec_eq_toMatrix := by intros; rfl
  gemv a b A x y :=
    let A := e.equiv A.1
    let x := e.equiv x.1
    let y := e.equiv y.1
    let y := BLAS.LevelTwoData.gemv .RowMajor .NoTrans
      (size m) (size n) a A 0 (size n) x 0 1 b y 0 1
    let y := e.equiv.symm y
    ⟨y, sorry_proof⟩
  gemv_spec := sorry_proof
  gemvT a b A x y :=
    let A := e.equiv A.1
    let x := e.equiv x.1
    let y := e.equiv y.1
    -- am I calling this right?
    let y := BLAS.LevelTwoData.gemv .RowMajor .Trans
      (size m) (size n) 1 A 0 (size n) x 0 1 0 y 0 1
    let y := e.equiv.symm y
    ⟨y, sorry_proof⟩
  gemvT_spec := sorry_proof
  gemvH a b A x y :=
    let A := e.equiv A.1
    let x := e.equiv x.1
    let y := e.equiv y.1
    let y := BLAS.LevelTwoData.gemv .RowMajor .ConjTrans
      (size m) (size n) 1 A 0 (size n) x 0 1 0 y 0 1
    let y := e.equiv.symm y
    ⟨y, sorry_proof⟩
  gemvH_spec := sorry_proof

open IndexType in
instance (R m n : Type*) (Array : outParam Type*)
    [RealScalar R] [PlainDataType R] [IndexType m] [IndexType n]
    [e : ScalarArray R Array] [LawfulBLAS Array R R] :
    MatrixType.Dense (R^[m,n]) where
  fromMatrix f := ⊞ i j => f i j
  right_inv' := sorry_proof
  set' A i j v := A.set (i,j) v
  set'_spec := sorry_proof
  row A i := A.curry[i]
  row_spec := sorry_proof
  sumRows A :=
    let A := e.equiv A.1
    ⊞ (i : m) => BLAS.LevelOneDataExt.sum (size n) A (toFin i * size n) 1
  sumRows_spec := sorry_proof
  col A j :=
    let A := e.equiv A.1
    have : Inhabited Array := ⟨A⟩
    let c := BLAS.LevelOneData.copy (size m) A (toFin j) (size n) (panic "col for R^[m,n] not implented!") 0 1
    ⟨e.equiv.symm c, sorry_proof⟩
  col_spec := sorry_proof
  sumCols A :=
    let A := e.equiv A.1
    ⊞ (j : n) => BLAS.LevelOneDataExt.sum (size m) A (toFin j) (size n)
  sumCols_spec := sorry_proof
  updateRow A i r :=
    let r := e.equiv r.1
    let A := e.equiv A.1
    let A := BLAS.LevelOneData.copy (size n) r 0 1 A (toFin i * size n) 1
    ⟨e.equiv.symm A, sorry_proof⟩
  updateRow_spec := sorry_proof
  updateCol A j c :=
    let c := e.equiv c.1
    let A := e.equiv A.1
    let A := BLAS.LevelOneData.copy (size m) c 0 1 A (toFin j) (size n)
    ⟨e.equiv.symm A, sorry_proof⟩
  updateCol_spec := sorry_proof
  outerprodAdd a x y A :=
    let A := e.equiv A.1
    let x := e.equiv x.1
    let y := e.equiv y.1
    let A := BLAS.LevelTwoData.ger .RowMajor (size m) (size n) a x 0 1 y 0 1 A 0 (size n)
    ⟨e.equiv.symm A, sorry_proof⟩
  outerprodAdd_spec := sorry_proof

-- open IndexType in
-- instance (R n : Type*) (Array : outParam Type*)
--     [RealScalar R] [PlainDataType R] [IndexType n]
--     [e : ScalarArray R Array] [LawfulBLAS Array R R] :
--     MatrixType.Square (R^[n,n]) where
--   diagonal d := sorry
--   diagonal_spec := sorry
--   diag := sorry
--   diag_spec := sorry

end Operations

end ScalarArrayEquiv
