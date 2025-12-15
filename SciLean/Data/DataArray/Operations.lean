import SciLean.Data.DataArray.DataArray
import SciLean.Data.DataArray.RnEquiv
import SciLean.Data.DataArray.Algebra
import SciLean.Data.DataArray.Float
import SciLean.Data.DataArray.FloatN
import SciLean.Meta.Notation.Let'
import SciLean.Data.ArrayOperations.Operations

import SciLean.Analysis.Scalar.FloatAsReal

namespace SciLean.DataArrayN

variable {X : Type*} [PlainDataType X] {I : Type*} {nI} [IndexType I nI] [Fold I]

/-- Transform all elements of `xs^[I]` using `f : X → X`. -/
abbrev mapMono (f : X → X) (xs : X^[I]) : X^[I] :=
  ArrayOps.mapMono f xs

/-- Transform all elements of `xs^[I]` using `f : I → X → X`. -/
abbrev mapIdxMono (f : I → X → X) (xs : X^[I]) : X^[I] :=
  ArrayOps.mapIdxMono f xs

/-- Element-wise map producing a new array. -/
@[inline]
def map {Y : Type*} [PlainDataType Y] (f : X → Y) (xs : X^[I]) : Y^[I] :=
  ofFn (coll := Y^[I]) fun i => f xs[i]

/-- Element-wise map with indices producing a new array. -/
@[inline]
def mapIdx {Y : Type*} [PlainDataType Y] (f : I → X → Y) (xs : X^[I]) : Y^[I] :=
  ofFn (coll := Y^[I]) fun i => f i xs[i]

/-- Combine two arrays element-wise producing a new array. -/
@[inline]
def zipWith {Y Z : Type*} [PlainDataType Y] [PlainDataType Z]
    (f : X → Y → Z) (xs : X^[I]) (ys : Y^[I]) : Z^[I] :=
  ofFn (coll := Z^[I]) fun i => f xs[i] ys[i]

/-- Combine two arrays element-wise, mutating `xs` if possible. -/
abbrev zipWithMono (f : X → X → X) (xs ys : X^[I]) : X^[I] :=
  ArrayOps.mapIdxMonoAcc (X:=X^[I]) (I:=I) (Y:=X) (Z:=X)
    (fun _ yi xi => f xi yi) (fun i => ys[i]) xs


----------------------------------------------------------------------------------------------------
-- Numpy-style convenience constructors ------------------------------------------------------------
----------------------------------------------------------------------------------------------------

/-- Numpy-style `arange`: `start + step*i` for `i = 0..n-1`. -/
@[inline]
def arange {R : Type*} [RealScalar R] [PlainDataType R]
    (n : Nat) (start : R := 0) (step : R := 1) : R^[n] :=
  ofFn (coll := R^[n]) fun (i : Idx n) => start + step * ((i : Nat) : R)

/-- Numpy-style `linspace` with `n` points. For `n ≤ 1` this returns `start` (or the empty array). -/
@[inline]
def linspace {R : Type*} [RealScalar R] [PlainDataType R]
    (n : Nat) (start stop : R) : R^[n] :=
  if n ≤ 1 then
    ofFn (coll := R^[n]) fun (_i : Idx n) => start
  else
    let denom : R := ((n - 1) : R)
    ofFn (coll := R^[n]) fun (i : Idx n) =>
      start + (stop - start) * ((i : Nat) : R) / denom

/-- Reverse a vector (Numpy: `flip`). -/
@[inline]
def reverse {n : Nat} (x : X^[n]) : X^[n] :=
  ⊞ (i : Idx n) =>
    let j : Idx n := ⟨(n - 1 - (i : Nat)).toUSize, sorry_proof⟩
    x[j]

/-- Identity matrix (Numpy: `eye`). -/
@[inline]
def eye {R : Type*} [RealScalar R] [PlainDataType R]
    (n : Nat) : R^[n,n] :=
  ⊞ (i : Idx n) (j : Idx n) =>
    if i = j then (1 : R) else 0

/-- Create a diagonal matrix from a vector (Numpy: `diag`). -/
@[inline]
def diag {R : Type*} [RealScalar R] [PlainDataType R]
    (n : Nat) (v : R^[n]) : R^[n,n] :=
  ⊞ (i : Idx n) (j : Idx n) =>
    if i = j then v[i] else 0

/-- Extract the diagonal of a square matrix (Numpy: `diagonal`). -/
@[inline]
def diagonal {R : Type*} [RealScalar R] [PlainDataType R]
    (n : Nat) (A : R^[n,n]) : R^[n] :=
  ofFn (coll := R^[n]) fun (i : Idx n) => A[i,i]

/-- Trace of a square matrix (Numpy: `trace`). -/
@[inline]
def trace {R : Type*} [RealScalar R] [PlainDataType R]
    (n : Nat) (A : R^[n,n]) : R :=
  ∑ᴵ (i : Idx n), A[i,i]

/-- Numpy-style `nonzero` for 1D arrays: return indices where `x[i] ≠ 0`. -/
@[inline]
def nonzeroIdx {R : Type*} [PlainDataType R] [Zero R] [DecidableEq R]
    (x : R^[I]) : Array I := Id.run do
  let mut idxs : Array I := #[]
  for i in fullRange I do
    if x[i] ≠ 0 then
      idxs := idxs.push i
  return idxs

/-- 2D border pattern: `border` on the boundary and `inside` in the interior. -/
@[inline]
def border2 {R : Type*} [RealScalar R] [PlainDataType R]
    (m n : Nat) (border inside : R) : R^[m,n] :=
  ⊞ (i : Idx m) (j : Idx n) =>
    let ii : Nat := i
    let jj : Nat := j
    let isBorder :=
      (ii == 0) || (ii == m - 1) || (jj == 0) || (jj == n - 1)
    if isBorder then border else inside

/-- Add a 1-cell padding border around a matrix. -/
@[inline]
def pad2 {R : Type*} [RealScalar R] [PlainDataType R]
    (m n : Nat) (A : R^[m,n]) (pad : R := 0) : R^[m+2,n+2] :=
  ⊞ (i : Idx (m+2)) (j : Idx (n+2)) =>
    let ii : Nat := i
    let jj : Nat := j
    let isPad :=
      (ii == 0) || (ii == m + 1) || (jj == 0) || (jj == n + 1)
    if isPad then
      pad
    else
      A[⟨(ii - 1).toUSize, sorry_proof⟩, ⟨(jj - 1).toUSize, sorry_proof⟩]

/-- Checkerboard pattern of `a`/`b` (Numpy exercises 19/21). -/
@[inline]
def checkerboard {R : Type*} [RealScalar R] [PlainDataType R]
    (m n : Nat) (a : R := 0) (b : R := 1) : R^[m,n] :=
  ⊞ (i : Idx m) (j : Idx n) =>
    if ((i : Nat) + (j : Nat)) % 2 = 0 then a else b

/-- Fold elements of `xs : X^[I]` using `op : α → X → α`.

It is just and abbreviation for a call to `IndexType.foldl` which runs a fold over the index
type `I`. -/
abbrev foldl (op : α → X → α) (init : α) (xs : X^[I]) : α :=
  IndexType.fold .full (init:=init) (fun i a => op a xs[i])

/-- Reduce elements of `xs : X^[I]` using `op : X → X → X`.

It is just and abbreviation for a call to `IndexType.reduce` which does reduction over the index
type `I`. -/
abbrev reduce [Inhabited X] (op : X → X → X) (xs : X^[I]) : X :=
  IndexType.reduce .full (fun (i:I) => xs[i]) op


/-- Reshape array to one dimensional array of `n` elements. -/
abbrev reshape1 (x : X^[I]) (m : Nat) (h : m = nI) : X^[m] :=
  x.reshape (Idx m) h

/-- Reshape array to two dimensional array. -/
abbrev reshape2 (x : X^[I]) (m₁ m₂ : Nat) (h : m₁*m₂ = nI) : X^[m₁,m₂] :=
  x.reshape (Idx m₁ × Idx m₂) h

/-- Reshape array to three dimensional array. -/
abbrev reshape3 (x : X^[I]) (m₁ m₂ m₃ : Nat) (h : m₁*(m₂*m₃) = nI) : X^[m₁,m₂,m₃] :=
  x.reshape (Idx m₁ × Idx m₂ × Idx m₃) h




section OverReals

variable
  {R : Type*} [RealScalar R] [pd : PlainDataType R]
  [Fold I]
  {ι nι} [IndexType ι nι] [Fold ι]
  [HasRnEquiv X ι R]


/--
Map real scalars of `x : X^[I]` by `f : R → R`.

It is required that `X ≃ R^[ι]` for some `ι`

The function `f` provides two indices `(i : X)` and `(j : ι)`
  - `i` maps to the particular `X`
  - `j` maps to the particular real scalar in `X`

Note that calling this function on `R^[n]` will give you `j : Unit`.
-/
@[reducible, inline, specialize, macro_inline]
def rmapIdx (f : I → ι → R → R) (x : X^[I]) : X^[I] :=
  ArrayOps.mapIdxMono
    (fun ij : I×ι =>
      let' (i,j) := ij
      f i j) x

/--
Map real scalars of `x : X^[I]` by `f : R → R`.

It is required that `X ≃ R^[ι]` for some `ι`
-/
@[reducible, inline, specialize, macro_inline]
def rmap (f : R → R) (x : X^[I]) : X^[I] :=
  rmapIdx (fun _ _ => f) x

/--
Map2 real scalars of `x y : X^[I]` by `f : R → R → R`

The first argument `x` is mutated if possible.

It is required that `X ≃ R^[ι]` for some `ι`

The function `f` provides two indices `(i : X)` and `(j : ι)`
  - `i` maps to the particular `X` in `X^[I]`
  - `j` maps to the particular real scalar `R` in `X`

Note that calling this function on `R^[n]` will give you `j : Unit`.

TODO: make this function to decide whether to mutate `x` or `y`
-/
@[reducible, inline, specialize, macro_inline]
def rmapIdx2 (f : I → ι → R → R → R) (x y : X^[I]) : X^[I] :=
  ArrayOps.mapIdxMonoAcc
    (fun (idx : I×ι) xi =>
      let' (i,j) := idx
      (f i j · xi))
    (fun idx => y[idx])
    x


/--
Map2 real scalars of `x y : X^[I]` by `f : R → R → R`

The first argument `x` is mutated if possible.

It is required that `X ≃ R^[J]` for some `J`

TODO: make this function to decide whether to mutate `x` or `y`
-/
@[reducible, inline, specialize, macro_inline]
def rmap2 (f : R → R → R) (x y : X^[I]) : X^[I] :=
  rmapIdx2 (fun _ _ => f) x y




----------------------------------------------------------------------------------------------------
-- Linear algebra ----------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

def minor
    {n} (A : R^[n+1,n+1] ) (i j : Idx (n+1)) : R^[n,n] :=
  ⊞ (i' j' : Idx n) =>
    let i'' : Idx (n+1) := if i'.1 < i.1 then i'.castSucc else i'.succ
    let j'' : Idx (n+1) := if j'.1 < j.1 then j'.castSucc else j'.succ
    A[i'',j'']

def det {n} (A : R^[n,n]) : R :=
  match n with
  | 0 => 1
  | n+1 =>
    ∑ᴵ (j : Idx (n+1)),
      let a0j := A[0,j]
      let M0j := A.minor 0 j
      let m0j := det M0j
      (-1)^(j.1.toNat) * a0j * m0j

-- def fromMinor
--     {n} (M : R^[n,n] ) (i j : Idx (n+1)) : R^[n+1,n+1] :=
--   (adjoint Float (fun A : Float^[n+1,n+1] => A.minor i j) M)
--   rewrite_by
--     unfold DataArrayN.minor
--     simp -zeta [Function.HasUncurry.uncurry] -- todo: add uncurry theorem for adjoint
--     lsimp only [simp_core,adjoint_simproc]


-- def _root_.SciLean.DataArrayN.addMinor
--     {n} (A : Float^[n+1,n+1]) (i j : Idx (n+1)) (M : Float^[n,n] ) : Float^[n+1,n+1] :=
--   (adjointUpdate Float (fun A : Float^[n+1,n+1] => A.minor i j) M A)
--   rewrite_by
--     unfold DataArrayN.minor
--     simp -zeta [Function.HasUncurry.uncurry] -- todo: add uncurry theorem for adjoint
--     lsimp only [simp_core,adjointUpdate_simproc]
