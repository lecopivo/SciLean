module

public import SciLean.Data.Idx
public import SciLean.Data.ArrayOperations.Basic

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum

@[expose] public section


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

theorem IndexType.left_inv' {I n} [IndexType I n] (h : n < USize.size) :
    LeftInverse fromIdx (toIdx : I → Idx n) := by
  intro i
  rw [IndexType.fromIdx_eq_fromFin]
  have h1 : (toIdx i).toFin = toFin i := Fin.ext (IndexType.toFin_eq_toIdx i h).symm
  rw [h1, IndexType.left_inv]

theorem IndexType.right_inv' {I n} [IndexType I n] (h : n < USize.size) :
    RightInverse fromIdx (toIdx : I → Idx n) := by
  intro j
  have h1 := IndexType.toFin_eq_toIdx (I:=I) (fromIdx j) h
  rw [IndexType.fromIdx_eq_fromFin, IndexType.right_inv] at h1
  apply Idx.eq_of_val_eq
  apply USize.toNat_inj.mp
  rw [IndexType.fromIdx_eq_fromFin, ← h1]
  rfl

def idxEquiv (I : Type*) {n} [IndexType I n] (h : n < USize.size) : I ≃ Idx n :=
  {
    toFun := toIdx
    invFun := fromIdx
    left_inv := IndexType.left_inv' h
    right_inv := IndexType.right_inv' h
  }

namespace IndexType

variable {I n} [IndexType I n]

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
  toFin_eq_toIdx := by decide
  fromIdx_eq_fromFin := by decide
  left_inv := by decide
  right_inv := by intro i; exact i.elim0


instance : IndexType Unit 1 where
  toIdx _ := 0
  fromIdx _ := ()
  toFin _ := 0
  fromFin _ := ()
  toFin_eq_toIdx := by aesop
  fromIdx_eq_fromFin := by decide
  left_inv := by decide
  right_inv := by decide


instance : IndexType Bool 2 where
  toIdx x := match x with | false => 0 | true => 1
  fromIdx x := if x = 0 then false else true
  toFin x := match x with | false => 0 | true => 1
  fromFin x := if x = 0 then false else true
  toFin_eq_toIdx := by
    intro x _
    cases x
    · decide
    · simp only [OfNat.ofNat, Idx.ofNat]
      simp [Fin.ofNat, usize_modn_toNat]
  fromIdx_eq_fromFin := by
    intro i
    have h : (i.toFin = 0) ↔ (i = 0) := by
      constructor
      · intro hf
        apply Idx.eq_of_val_eq
        rw [← USize.toNat_inj, show ((0 : Idx 2) : USize).toNat = 0 from rfl]
        simpa [Idx.toFin, Fin.ext_iff] using hf
      · rintro rfl; rfl
    simp [h]
  left_inv := by decide
  right_inv := by decide


instance : IndexType (Fin n) n where
  toIdx x := x.toIdx
  fromIdx x := x.toFin
  toFin x := x
  fromFin x := x
  toFin_eq_toIdx := by intro x h; show (x:ℕ) = (x.1.toUSize).toNat; rw [USize.toNat_ofNat']; exact (Nat.mod_eq_of_lt (Nat.lt_trans x.isLt h)).symm
  fromIdx_eq_fromFin := by simp
  left_inv := by grind
  right_inv := by intro i; rfl


instance : IndexType (Idx n) n where
  toIdx x := x
  fromIdx x := x
  toFin x := x.toFin
  fromFin x := x.toIdx
  toFin_eq_toIdx := by aesop
  fromIdx_eq_fromFin := by intro i; apply Idx.eq_of_val_eq; simp [Idx.toFin, Fin.toIdx]
  left_inv := by intro i; apply Idx.eq_of_val_eq; simp [Idx.toFin, Fin.toIdx]
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
  toIdx := fun (a,b) => ⟨nJ.toUSize * toIdx a + toIdx b, by
    have ha := (toIdx a).2
    have hb := (toIdx b).2
    rcases Nat.lt_or_ge (nI*nJ) USize.size with hN | hN
    · have hbound : nJ * (toIdx a).1.toNat + nJ ≤ nI * nJ := by
        rw [Nat.mul_comm nI nJ, ← Nat.mul_succ]
        exact Nat.mul_le_mul_left _ ha
      have hnJ : nJ ≤ nI * nJ := Nat.le_mul_of_pos_left nJ (Nat.zero_lt_of_lt ha)
      have e1 : nJ.toUSize.toNat = nJ := usize_toNat_ofNat_eq (by omega)
      have e2 : (nJ.toUSize * (toIdx a).1).toNat = nJ * (toIdx a).1.toNat := by
        rw [usize_toNat_mul_eq (by rw [e1]; omega), e1]
      rw [usize_toNat_add_eq (by rw [e2]; omega), e2]
      omega
    · exact Nat.lt_of_lt_of_le (USize.toNat_lt_size _) hN⟩
  fromIdx ij :=
    -- this choice will result in row major matrices
    let i : Idx nI := ⟨ij.1 / nJ.toUSize, by sorry_proof⟩
    let j : Idx nJ := ⟨ij.1 % nJ.toUSize, by
      have hx := ij.2
      have hpos : 0 < nJ := Nat.pos_of_ne_zero (by rintro rfl; simp at hx)
      rw [USize.toNat_mod, USize.toNat_ofNat']
      rcases Nat.eq_zero_or_pos (nJ % 2 ^ System.Platform.numBits) with h | h
      · rw [h, Nat.mod_zero]
        have := USize.toNat_lt_two_pow_numBits ij.1
        have := Nat.le_of_dvd hpos (Nat.dvd_of_mod_eq_zero h)
        omega
      · exact lt_of_lt_of_le (Nat.mod_lt _ h) (Nat.mod_le _ _)⟩
    (fromIdx i, fromIdx j)
  toFin := fun (a,b) => ⟨nJ * (toFin a).1 + (toFin b).1, by
    have h : nJ * (toFin a).1 + nJ ≤ nI * nJ := by
      rw [Nat.mul_comm nI nJ, ← Nat.mul_succ]
      exact Nat.mul_le_mul_left _ (toFin a).isLt
    have := (toFin b).isLt
    omega⟩
  fromFin ij :=
    -- this choice will result in row major matrices
    let i : Fin nI := ⟨ij.1 / nJ, Nat.div_lt_of_lt_mul (Nat.mul_comm nI nJ ▸ ij.isLt)⟩
    let j : Fin nJ := ⟨ij.1 % nJ, Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => by
      have := ij.isLt; simp [h] at this)⟩
    (fromFin i, fromFin j)
  toFin_eq_toIdx := by
    rintro ⟨i,j⟩ h
    have hnI : nI ≠ 0 := by rintro rfl; exact absurd (toFin i).isLt (by omega)
    have hnJ : nJ ≠ 0 := by rintro rfl; exact absurd (toFin j).isLt (by omega)
    have hI : nI < USize.size :=
      Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hnJ)) h
    have hJ : nJ < USize.size :=
      Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hnI)) h
    have hi := (toIdx i).2
    have hj := (toIdx j).2
    have key : nJ * (toIdx i).1.toNat + (toIdx j).1.toNat < nI * nJ :=
      calc nJ * (toIdx i).1.toNat + (toIdx j).1.toNat
          < nJ * (toIdx i).1.toNat + nJ := Nat.add_lt_add_left hj _
        _ = nJ * ((toIdx i).1.toNat + 1) := (Nat.mul_succ _ _).symm
        _ ≤ nJ * nI := Nat.mul_le_mul_left _ hi
        _ = nI * nJ := Nat.mul_comm _ _
    have e1 : nJ.toUSize.toNat = nJ := usize_toNat_ofNat_eq hJ
    have e2 : (nJ.toUSize * (toIdx i).1).toNat = nJ * (toIdx i).1.toNat := by
      rw [usize_toNat_mul_eq (by rw [e1]; omega), e1]
    show nJ * (toFin i).1 + (toFin j).1 = (nJ.toUSize * (toIdx i).1 + (toIdx j).1).toNat
    rw [usize_toNat_add_eq (by rw [e2]; omega), e2,
      IndexType.toFin_eq_toIdx i hI, IndexType.toFin_eq_toIdx j hJ]
  fromIdx_eq_fromFin := sorry_proof
  left_inv := by
    rintro ⟨a,b⟩
    have hj := (toFin b).isLt
    have hpos : 0 < nJ := Nat.pos_of_ne_zero fun h => by simp [h] at hj
    have h1 : (nJ * (toFin a).1 + (toFin b).1) / nJ = (toFin a).1 := by
      rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt hj, Nat.add_zero]
    have h2 : (nJ * (toFin a).1 + (toFin b).1) % nJ = (toFin b).1 := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
    show (fromFin ⟨_,_⟩, fromFin ⟨_,_⟩) = (a,b)
    rw [show (⟨_,_⟩ : Fin nI) = toFin a from Fin.ext h1,
        show (⟨_,_⟩ : Fin nJ) = toFin b from Fin.ext h2,
        IndexType.left_inv a, IndexType.left_inv b]
  right_inv := by
    intro ij
    apply Fin.ext
    dsimp only
    rw [show ∀ (x : Fin nI), toFin (fromFin x : I) = x from IndexType.right_inv,
        show ∀ (x : Fin nJ), toFin (fromFin x : J) = x from IndexType.right_inv]
    exact Nat.div_add_mod _ _


instance {α β} [IndexType α m] [IndexType β n] : IndexType (α ⊕ β) (m + n) where
  toIdx := fun ab =>
    match ab with
    | .inl a => ⟨(toIdx a).1, by have := (toIdx a).2; omega⟩
    | .inr b => ⟨m.toUSize + (toIdx b).1, by
      have h1 := usize_toNat_add_le m.toUSize (toIdx b).1
      have h2 := usize_toNat_ofNat_le m
      have h3 := (toIdx b).2
      omega⟩
  fromIdx ij :=
    if h : ij.1 < m.toUSize then
      .inl (fromIdx ⟨ij.1, Nat.lt_of_lt_of_le (USize.lt_iff_toNat_lt.1 h) (usize_toNat_ofNat_le m)⟩)
    else
      .inr (fromIdx ⟨ij.1 - m.toUSize,sorry_proof⟩)
  toFin := fun ab =>
    match ab with
    | .inl a => ⟨(toFin a).1, by omega⟩
    | .inr b => ⟨m + (toFin b).1, by simp⟩
  fromFin ij :=
    if h : ij.1 < m then
      .inl (fromFin ⟨ij.1, by aesop⟩)
    else
      .inr (fromFin ⟨ij.1 - m,by omega⟩)
  toFin_eq_toIdx := by
    intro ab h
    have hm : m < USize.size := by omega
    have hn : n < USize.size := by omega
    cases ab with
    | inl a => exact IndexType.toFin_eq_toIdx a hm
    | inr b =>
      have hb := (toIdx b).2
      have e1 : m.toUSize.toNat = m := usize_toNat_ofNat_eq hm
      show m + (toFin b).1 = (m.toUSize + (toIdx b).1).toNat
      rw [usize_toNat_add_eq (by rw [e1]; omega), e1, IndexType.toFin_eq_toIdx b hn]
  fromIdx_eq_fromFin := sorry_proof
  left_inv := by
    rintro (a | b) <;> dsimp only
    · simp only [(toFin a).isLt, ↓reduceDIte, Fin.eta,
        show ∀ (x : α), fromFin (toFin x) = x from IndexType.left_inv]
    · simp only [Nat.not_lt.2 (Nat.le_add_right m _), ↓reduceDIte,
        show (⟨m + (toFin b).1 - m, by omega⟩ : Fin n) = toFin b from
          Fin.ext (Nat.add_sub_cancel_left m (toFin b).1),
        show ∀ (x : β), fromFin (toFin x) = x from IndexType.left_inv]
  right_inv := by
    intro ij
    dsimp only
    by_cases h : (ij : ℕ) < m
    · simp only [h, ↓reduceDIte]
      apply Fin.ext
      dsimp only
      rw [show ∀ (x : Fin m), toFin (fromFin x : α) = x from IndexType.right_inv]
    · simp only [h, ↓reduceDIte]
      apply Fin.ext
      dsimp only
      rw [show ∀ (x : Fin n), toFin (fromFin x : β) = x from IndexType.right_inv]
      exact Nat.add_sub_cancel' (Nat.not_lt.1 h)


@[instance_reducible]
def ofEquiv {J : Type*} (I : Type*) [Fintype J] [IndexType I n] (f : I ≃ J) : IndexType J n where
  toIdx y := toIdx (f.symm y)
  fromIdx i := f (fromIdx i)
  toFin y := toFin (f.symm y)
  fromFin i := f (fromFin i)
  toFin_eq_toIdx := fun y h => IndexType.toFin_eq_toIdx (f.symm y) h
  fromIdx_eq_fromFin := fun i => congrArg f (IndexType.fromIdx_eq_fromFin i)
  left_inv := by
    intro y
    show f (fromFin (toFin (f.symm y))) = y
    rw [IndexType.left_inv]
    exact f.apply_symm_apply y
  right_inv := by
    intro i
    show toFin (f.symm (f (fromFin i))) = i
    simp [IndexType.right_inv i]



end Instances
