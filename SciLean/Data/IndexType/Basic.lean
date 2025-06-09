import SciLean.Data.Idx
import SciLean.Data.ArrayOperations.Basic

import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

namespace SciLean

open Function


/--
Type `I` is isomorphic to `Idx n` and `Fin n`

The isomorphism with `Idx n` is required only if the size of `I` is smaller then `USize.size`.
In applications, we can't work with larger types as they would not fit into memory.
-/
class IndexType (I : Type*) (n : outParam Nat) extends Fintype I, Size' I n where
  toIdx : I → Idx n
  fromIdx : Idx n → I

  toFin : I → Fin n
  fromFin : Fin n→ I

  toFin_eq_toIdx (i : I) (h : n < USize.size) : toFin i = (toIdx i : ℕ)
  fromIdx_eq_fromFin (i : Idx n) :
    (fromIdx i : I) = (fromFin i.toFin : I)

  left_inv : LeftInverse fromFin toFin
  right_inv : RightInverse fromFin toFin

export IndexType (toIdx fromIdx)

set_option linter.unusedVariables false in
def idxEquiv (I : Type*) {n} [IndexType I n] (h : n < USize.size) : I ≃ Idx n :=
  {
    toFun := toIdx
    invFun := fromIdx
    left_inv := sorry_proof
    right_inv := sorry_proof
  }

namespace IndexType

variable {I n} [IndexType I n]

set_option linter.unusedVariables false in
theorem left_inv' (h : n < USize.size) :  LeftInverse fromIdx (toIdx : I → Idx n) := sorry_proof

set_option linter.unusedVariables false in
theorem right_inv' (h : n < USize.size) :  RightInverse fromIdx (toIdx : I → Idx n) := sorry_proof

@[simp, simp_core]
theorem toIdx_fromIdx (i : Idx n) : toIdx (fromIdx i : I) = i := by
  have hsize : n < USize.size := by sorry_proof
  apply right_inv' hsize

@[simp, simp_core]
theorem fromIdx_toIdx (i : I) : fromIdx (toIdx i) = i := by
  have hsize : n < USize.size := by sorry_proof
  apply left_inv' hsize


----------------------------------------------------------------------------------------------------
-- Instances ---------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section Instances

instance : IndexType Empty 0 where
  toIdx x := Empty.elim x
  fromIdx i := by have := i.2; aesop
  toFin x := Empty.elim x
  fromFin i := by have := i.2; aesop
  toFin_eq_toIdx := sorry_proof
  fromIdx_eq_fromFin := sorry_proof
  left_inv := sorry_proof
  right_inv := sorry_proof


instance : IndexType Unit 1 where
  toIdx _ := 0
  fromIdx _ := ()
  toFin _ := 0
  fromFin _ := ()
  toFin_eq_toIdx := sorry_proof
  fromIdx_eq_fromFin := sorry_proof
  left_inv := sorry_proof
  right_inv := sorry_proof


instance : IndexType Bool 2 where
  toIdx x := match x with | false => 0 | true => 1
  fromIdx x := if x = 0 then false else true
  toFin x := match x with | false => 0 | true => 1
  fromFin x := if x = 0 then false else true
  toFin_eq_toIdx := sorry_proof
  fromIdx_eq_fromFin := sorry_proof
  left_inv := sorry_proof
  right_inv := sorry_proof


instance : IndexType (Fin n) n where
  toIdx x := x.toIdx
  fromIdx x := x.toFin
  toFin x := x
  fromFin x := x
  toFin_eq_toIdx := sorry_proof
  fromIdx_eq_fromFin := sorry_proof
  left_inv := sorry_proof
  right_inv := sorry_proof


instance : IndexType (Idx n) n where
  toIdx x := x
  fromIdx x := x
  toFin x := x.toFin
  fromFin x := x.toIdx
  toFin_eq_toIdx := sorry_proof
  fromIdx_eq_fromFin := sorry_proof
  left_inv := sorry_proof
  right_inv := sorry_proof

instance : IndexType (Idx2 a b) (b-a+1).toNat where
  toIdx x := x.toIdx
  fromIdx x := x.toIdx2
  toFin x := x.toFin
  fromFin x := x.toIdx2
  toFin_eq_toIdx := sorry_proof
  fromIdx_eq_fromFin := sorry_proof
  left_inv := sorry_proof
  right_inv := sorry_proof

@[inline]
instance {I J nI nJ} [IndexType I nI] [IndexType J nJ] : IndexType (I × J) (nI*nJ) where
  -- this choice will result in row major matrices/tensors
  toIdx := fun (a,b) => ⟨nJ.toUSize * toIdx a + toIdx b, by sorry_proof⟩
  fromIdx ij :=
    -- this choice will result in row major matrices
    let i : Idx nI := ⟨ij.1 / nJ.toUSize, by sorry_proof⟩
    let j : Idx nJ := ⟨ij.1 % nJ.toUSize, by sorry_proof⟩
    (fromIdx i, fromIdx j)
  toFin := fun (a,b) => ⟨nJ * (toFin a).1 + (toFin b).1, by sorry_proof⟩
  fromFin ij :=
    -- this choice will result in row major matrices
    let i : Fin nI := ⟨ij.1 / nJ, by sorry_proof⟩
    let j : Fin nJ := ⟨ij.1 % nJ, by sorry_proof⟩
    (fromFin i, fromFin j)
  toFin_eq_toIdx := sorry_proof
  fromIdx_eq_fromFin := sorry_proof
  left_inv := by intro; sorry_proof
  right_inv := by intro; sorry_proof


instance {α β} [IndexType α m] [IndexType β n] : IndexType (α ⊕ β) (m + n) where
  toIdx := fun ab =>
    match ab with
    | .inl a => ⟨(toIdx a).1, by sorry_proof⟩
    | .inr b => ⟨m.toUSize + (toIdx b).1, by sorry_proof⟩
  fromIdx ij :=
    if h : ij.1 < m.toUSize then
      .inl (fromIdx ⟨ij.1,sorry_proof⟩)
    else
      .inr (fromIdx ⟨ij.1 - m.toUSize,sorry_proof⟩)
  toFin := fun ab =>
    match ab with
    | .inl a => ⟨(toFin a).1, by sorry_proof⟩
    | .inr b => ⟨m + (toFin b).1, by sorry_proof⟩
  fromFin ij :=
    if h : ij.1 < m then
      .inl (fromFin ⟨ij.1,sorry_proof⟩)
    else
      .inr (fromFin ⟨ij.1 - m,sorry_proof⟩)
  toFin_eq_toIdx := sorry_proof
  fromIdx_eq_fromFin := sorry_proof
  left_inv := by intro; sorry_proof
  right_inv := by intro; sorry_proof


def ofEquiv {J : Type*} (I : Type*) [Fintype J] [IndexType I n] (f : I ≃ J) : IndexType J n where
  toIdx y := toIdx (f.symm y)
  fromIdx i := f (fromIdx i)
  toFin y := toFin (f.symm y)
  fromFin i := f (fromFin i)
  toFin_eq_toIdx := sorry_proof
  fromIdx_eq_fromFin := sorry_proof
  left_inv := sorry_proof
  right_inv := sorry_proof



end Instances
