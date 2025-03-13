import SciLean.Data.DataArray.DataArray
import SciLean.Data.ArrayOperations.Operations

namespace SciLean.DataArrayN

variable {X : Type*} [PlainDataType X] {I : Type*} {n} [IdxType I n] [IdxType.Fold' I]

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
  IdxType.fold .full (init:=init) (fun i a => op a xs[i])

/-- Reduce elements of `xs : X^[I]` using `op : X → X → X`.

It is just and abbreviation for a call to `IndexType.reduce` which does reduction over the index
type `I`. -/
abbrev reduce [Inhabited X] (op : X → X → X) (xs : X^[I]) : X :=
  IdxType.reduce .full (fun (i:I) => xs[i]) op


/-- Reshape array to one dimensional array of `n` elements. -/
abbrev reshape1 (x : X^[I]) (m : Nat) (h : m = n) : X^[m] :=
  x.reshape (Idx m) h

/-- Reshape array to two dimensional array. -/
abbrev reshape2 (x : X^[I]) (m₁ m₂ : Nat) (h : m₁*m₂ = n) : X^[m₁,m₂] :=
  x.reshape (Idx m₁ × Idx m₂) h

/-- Reshape array to three dimensional array. -/
abbrev reshape3 (x : X^[I]) (m₁ m₂ m₃ : Nat) (h : m₁*(m₂*m₃) = n) : X^[m₁,m₂,m₃] :=
  x.reshape (Idx m₁ × Idx m₂ × Idx m₃) h
