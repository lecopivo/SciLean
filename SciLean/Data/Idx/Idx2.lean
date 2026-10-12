module

public import Mathlib.Topology.Order

public import SciLean.Util.SorryProof
public import SciLean.Data.IndexType.Init
public import SciLean.Data.Idx.Basic
public import SciLean.Data.Int64

@[expose] public section


namespace SciLean

/--
`Idx2 a b` is a whole number `i` with the constraint `a ≤ i ≤ b` -/
structure Idx2 (a b : ℤ) where
  val  : Int64
  bounds : a ≤ val.toInt ∧ val.toInt ≤ b

attribute [coe] Idx2.val

theorem Idx2.eq_of_val_eq {a b} : ∀ {i j : Idx2 a b}, Eq i.val j.val → Eq i j
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem Idx2.val_eq_of_eq {a b} {i j : Idx2 a b} (h : Eq i j) : Eq i.val j.val :=
  h ▸ rfl

instance {a b} : DecidableEq (Idx2 a b) :=
  fun i j =>
    if h : i.val = j.val then
      .isTrue (Idx2.eq_of_val_eq h)
    else
      .isFalse (fun h' => h (Idx2.val_eq_of_eq h'))
    -- probably too slow
    -- match decEq i.val j.val with
    -- | isTrue h  => isTrue (Idx.eq_of_val_eq h)
    -- | isFalse h => isFalse (fun h' => absurd (Idx.val_eq_of_eq h') h)

instance {a b} : LT (Idx2 a b) where
  lt a b := LT.lt a.val b.val

instance {a b} : LE (Idx2 a b) where
  le a b := LE.le a.val b.val

instance Idx2.decLt {a b} (i j : Idx2 a b) : Decidable (LT.lt i j) := -- Nat.decLt .. -- too slow
  if h : i.val < j.val then
    .isTrue h
  else
    .isFalse h
instance Idx2.decLe {a b} (i j : Idx2 a b) : Decidable (LE.le i j) :=  -- Nat.decLe .. -- too slow
  if h : i.val ≤ j.val then
    .isTrue h
  else
    .isFalse h


/-- The offset `i - a` (computed in `Int64`, clamped at `0`) is below the size of `Idx2 a b`.
This holds even when `i - a` wraps around. -/
theorem Idx2.toNatClampNeg_sub_lt {a b : ℤ} (i : Idx2 a b) :
    (i.1 - a.toInt64).toNatClampNeg < (b-a+1).toNat := by
  have h := i.2
  simp only [Int64.toNatClampNeg, Int64.toInt_sub, Int.toInt64, Int64.toInt_ofInt, Int64.size]
  rw [Int.bmod_def, Int.bmod_def]
  split_ifs <;> omega

/-- The offset `i - a` (computed in `Int64`, converted to `USize`) is below the size of `Idx2 a b`.
This holds even when `i - a` wraps around. -/
theorem Idx2.toUSize_sub_lt {a b : ℤ} (i : Idx2 a b) :
    (i.1 - a.toInt64).toUSize.toNat < (b-a+1).toNat := by
  have h := i.2
  have hu : ∀ x : Int64, (x.toUSize.toNat : Int) = x.toInt % 2 ^ System.Platform.numBits := by
    intro x
    show ((BitVec.signExtend _ x.toBitVec).toNat : Int) = _
    rw [BitVec.signExtend, BitVec.toNat_ofInt, Int64.toInt_toBitVec, Int.toNat_of_nonneg]
    · norm_cast
    · exact Int.emod_nonneg _ (by simp)
  have hx := hu (i.1 - a.toInt64)
  simp only [Int64.toInt_sub, Int.toInt64, Int64.toInt_ofInt, Int64.size] at hx ⊢
  generalize (i.1 - Int64.ofInt a).toUSize.toNat = n at hx ⊢
  rw [Int.bmod_def, Int.bmod_def] at hx
  rcases System.Platform.numBits_eq with hn | hn <;> rw [hn] at hx <;> split_ifs at hx <;> omega

/--
`Idx2 a b` is equivalent to `Fin n`

This is blatanly false but we treat `Idx2 a b` as `Fin n`, see documentation of `Idx2 a b`.
-/
def Idx2.finEquiv (a b : ℤ) : Idx2 a b ≃ Fin ((b - a + 1).toNat) where
  toFun x := ⟨(x.1 - a.toInt64).toNatClampNeg, Idx2.toNatClampNeg_sub_lt x⟩
  invFun x := ⟨x.1.toInt64 + a.toInt64, sorry_proof⟩
  left_inv := sorry_proof
  right_inv := sorry_proof

-- The rest of the file is direct copy of `Init.Data.Fin.Basic`
namespace Idx2

def toFin (i : Idx2 a b) : Fin (b-a+1).toNat := ⟨(i.1 - a.toInt64).toNatClampNeg, toNatClampNeg_sub_lt i⟩
def _root_.Fin.toIdx2 {a b : ℤ} (i : Fin (b-a+1).toNat) : Idx2 a b := ⟨i.1.toInt64 + a.toInt64, sorry_proof⟩

def toIdx (i : Idx2 a b) : Idx (b-a+1).toNat := ⟨(i.1 - a.toInt64).toUSize, toUSize_sub_lt i⟩
def _root_.SciLean.Idx.toIdx2 {a b : ℤ} (i : Idx (b-a+1).toNat) : Idx2 a b := ⟨i.1.toInt64 + a.toInt64, sorry_proof⟩

instance coeToUSize : CoeOut (Idx2 a b) Int64 :=
  ⟨fun v => v.val⟩

instance coeToNat : CoeOut (Idx2 a b) ℤ :=
  ⟨fun v => v.val.toInt⟩

variable {a b : ℤ}

----------------------------------------------------------------------------------------------------

instance : ToString (Idx2 a b) := ⟨fun i => toString i.1⟩

instance : Fintype (Idx2 a b) := Fintype.ofEquiv _ (Idx2.finEquiv a b).symm

instance : Size (Idx2 a b) where
  size := (b - a + 1).toNat

instance : Size' (Idx2 a b) (b - a + 1).toNat where

instance : FirstLast (Idx2 a b) (Idx2 a b) where
  firstLast? :=
    if h : (a ≤ a.toInt64.toInt ∧ a.toInt64.toInt ≤ b) ∧ (a ≤ b.toInt64.toInt ∧ b.toInt64.toInt ≤ b) then
      some (⟨a.toInt64, h.1⟩, ⟨b.toInt64, h.2⟩)
    else
      none

-- instance : IndexType (Idx2 a b) (b - a + 1).toNat where
--   toFin x := x.toFin
--   fromFin x := x.toIdx
--   rangeSize := fun r =>
--     match r with
--     | .empty => 0
--     | .full => n
--     | .interval a b => if a.1 ≤ b.1 then ((b.1 - a.1) + 1).toNat else ((a.1 - b.1) + 1).toNat
--   next? s :=
--     match s with
--     | .start r =>
--       match r with
--       | .empty => none
--       | .full =>
--         if h : n ≠ 0 then
--           let x : Idx2 a b := ⟨0, by sorry_proof⟩
--           .some (x, .val x r)
--         else
--           .none
--       | .interval a _ => .some (a, .val a r)

--     | .val val r =>
--       match r with
--       | .empty => .none
--       | .full =>
--         if h : val.1 + 1 < n.toUSize then
--           let x := ⟨val.1+1, sorry_proof⟩
--           .some (x, .val x r)
--         else
--           .none
--       | .interval a b =>
--         if a.1 ≤ b.1 then
--           if h : val.1 + 1 ≤ b.1 then
--             let x := ⟨val.1+1, sorry_proof⟩
--             .some (x, .val x r)
--           else
--             .none
--         else
--           if h : b.1 + 1 ≤ val.1 then
--             let x := ⟨val.1-1, sorry_proof⟩
--             .some (x, .val x r)
--           else
--             .none
--   left_inv := sorry_proof
--   right_inv := sorry_proof
--   first_last := sorry_proof

-- maybe move these such that we do not have to import `Mathlib.Topology.Order`
instance {a b} : TopologicalSpace (Idx2 a b) := ⊥
instance {a b} : DiscreteTopology (Idx2 a b) := ⟨rfl⟩

end Idx2
