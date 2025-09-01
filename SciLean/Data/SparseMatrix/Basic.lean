import SciLean.Data.DataArray.DataArray
import SciLean.Meta.Notation.Do
-- import Mathlib

namespace SciLean

structure SparseMatrixUnassembled (R : Type*) [PlainDataType R] (I J : Type*)
    {nI} [IndexType I nI] {nJ} [IndexType J nJ] where

  row : DataArray (Fin nI)
  col : DataArray (Fin nJ)
  data : DataArray R

  size_data_eq_row : data.size = row.size
  size_data_eq_col : data.size = col.size


namespace SparseMatrixUnassembled

variable
  {R : Type*} [PlainDataType R] {I J : Type*}
  {nI} [IndexType I nI] {nJ} [IndexType J nJ]
  [DecidableEq I] [DecidableEq J]

def get [Zero R] [Add R] (A : SparseMatrixUnassembled R I J) (i : I) (j : J) : R := Id.run do

  let mut aij : R := 0

  let i := toIdx i
  let j := toIdx j

  for idx in fullRange (Idx A.data.size) do

    let i' := A.row.get (idx.cast A.size_data_eq_row) |>.toIdx
    if i' ≠ i then continue

    let j' := A.col.get (idx.cast A.size_data_eq_col) |>.toIdx
    if j' ≠ j then continue

    aij += A.data.get idx

  return aij

/-- Add to an element of sparse matrix.

This is **the** function to build sparse matrices element by element. -/
def add [Zero R] [Add R] (A : SparseMatrixUnassembled R I J) (i : I) (j : J) (v : R) :
    SparseMatrixUnassembled R I J :=
  let ⟨row,col,data,_,_⟩ := A
  ⟨row.push (IndexType.toFin i), col.push (IndexType.toFin j), data.push v, sorry_proof, sorry_proof⟩

end SparseMatrixUnassembled


-- TODO: change `Fin` to `Idx`
structure SparseMatrixAssembled (R : Type*) [PlainDataType R] (I J : Type*)
    {nI} [IndexType I nI] {nJ} [IndexType J nJ] where

  /-- Non-zero elements in a given column. -/
  indexMap : Vector (DataArray (Fin nI)) nJ
  /-- Values of non-zero elements in a given column. -/
  data : Vector (DataArray R) nJ

  -- the number of indices match the number of data
  h_size (j : Fin nJ) : (indexMap[j]).size = (data[j]).size
  -- rows are given in increasing order
  sorted_rows (j : Fin nJ) : (List.ofFn (fun i => (indexMap[j].get i.toIdx))).Sorted (·≤·)


namespace SparseMatrixAssembled

variable
  {R : Type*} [PlainDataType R] {I J : Type*}
  {nI} [IndexType I nI] {nJ} [IndexType J nJ]
  [DecidableEq I] [DecidableEq J]

def get [Zero R] (A : SparseMatrixAssembled R I J) (i : I) (j : J) : R := Id.run do

  let i := IndexType.toFin i
  let j := IndexType.toFin j
  let is := A.indexMap[j]

  -- this loop assumes that indices are sorted!
  for idx in fullRange (Idx is.size) do
    let i' := is.get idx
    -- return if we find non-zero row
    if i' == i then
      return A.data[j].get (A.h_size j ▸ idx)
    -- stop if `i'` is larger than the row we want
    else if i' > i then
      return 0

  return 0

end SparseMatrixAssembled


namespace SparseMatrix

inductive Repr (R : Type*) [PlainDataType R] (I J : Type*)
    {nI} [IndexType I nI] {nJ} [IndexType J nJ] where
  | unassembled (A : SparseMatrixUnassembled R I J)
  | colMajor (A : SparseMatrixAssembled R I J)
  | rowMajor (A : SparseMatrixAssembled R J I)

namespace Repr

variable {R : Type*} [PlainDataType R] [Zero R] [Add R] {I J : Type*}
    {nI} [IndexType I nI] {nJ} [IndexType J nJ]

def get (A : Repr R I J) (i : I) (j : J) : R :=
  match A with
  | .unassembled A => A.get i j
  | .colMajor A => A.get i j
  | .rowMajor A => A.get j i

end Repr


variable (R : Type*) [PlainDataType R] [Zero R] [Add R] (I J : Type*)
    {nI} [IndexType I nI] {nJ} [IndexType J nJ]

instance setoid : Setoid (Repr R I J) where
  r A B := ∀ i j, A.get i j = B.get i j
  iseqv := {
    refl := by simp
    symm := by intros; simp_all
    trans := by intros; simp_all
  }

end SparseMatrix

-- TODO: move this
/--
Class deciding whether `r : R` is zero up to rounding errors.

Semantics of this function is that it gives you zero exactly but in practice we break consistency
and small enough elements are considered zero too.
 -/
class ApproxZero (R : Type*) [Zero R] where
  approxZero : R → Bool
  is_zero (r : R) : approxZero r ↔ r = 0


-- TODO: maybe expose row/col major into the type such that you do not accidantely work with
--       a mixture of row/col major matrices which would be slow

/-- Sparse matrix with values in `R` index by `I` and `J`

There are three different formats of sparse matrix
  - *unassembled* - stores and array of `(i,j,aᵢⱼ)`, this format is used for building sparse matrix
    element by element
  - *row/col major* - for every row `i`/col `j` it stores an array of `(j,aᵢⱼ)`/`(i,aᵢⱼ)` non-zero
    elements sorted by `j`/`i` in asscending order
g-/
def SparseMatrix
    (R : Type*) [PlainDataType R] [Zero R] [Add R]
    (I J : Type*) {nI} [IndexType I nI] {nJ} [IndexType J nJ] : Type :=
  Quotient (SparseMatrix.setoid R I J)
