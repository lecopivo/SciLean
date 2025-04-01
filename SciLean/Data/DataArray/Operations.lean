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
