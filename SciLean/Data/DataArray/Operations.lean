import SciLean.Data.DataArray.DataArray
import SciLean.Data.ArrayOperations.Operations

namespace SciLean.DataArrayN

variable {X : Type*} [PlainDataType X] {I : Type*} [IndexType I]

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
  IndexType.foldl (init:=init) (fun a i => op a xs[i])

/-- Reduce elements of `xs : X^[I]` using `op : X → X → X`.

It is just and abbreviation for a call to `IndexType.reduce` which does reduction over the index
type `I`. -/
abbrev reduce [Inhabited X] (op : X → X → X) (xs : X^[I]) : X :=
  IndexType.reduce (fun (i:I) => xs[i]) op


/-- Reshape array to one dimensional array of `n` elements. -/
abbrev reshape1 (x : X^[I]) (n : Nat) (h : size I = n) : X^[n] :=
  x.reshape (Fin n) (by simp_all)

/-- Reshape array to two dimensional array. -/
abbrev reshape2 (x : X^[I]) (m n : Nat) (h : size I = m*n) : X^[m,n] :=
  x.reshape (Fin m × Fin n) (by simp_all)

/-- Reshape array to three dimensional array. -/
abbrev reshape3 (x : X^[I]) (l m n : Nat) (h : size I = l*m*n) : X^[l,m,n] :=
  x.reshape (Fin l × Fin m × Fin n) (by simp_all; ac_rfl)
