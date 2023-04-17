import SciLean.Mathlib.Data.Enumtype
-- import SciLean.Core.Functions

namespace SciLean

/--
Similar to `Fin n` but uses `USize` internally instead of `Nat`

WARRNING: Needs serious revision such that overflows are handled correctly!
-/
structure Idx (n : USize) where
  val : USize
  property : val < n
  -- Maybe add this assumption then adding two `Idx n` won't cause overflow
  -- not_too_big : n < (USize.size/2).toUSize
deriving DecidableEq

instance : ToString (Idx n) := ⟨λ i => toString i.1⟩

instance {n} : LT (Idx n) where
  lt a b := a.val < b.val

instance {n} : LE (Idx n) where
  le a b := a.val ≤ b.val

instance Idx.decLt {n} (a b : Idx n) : Decidable (a < b) := USize.decLt ..
instance Idx.decLe {n} (a b : Idx n) : Decidable (a ≤ b) := USize.decLe ..

namespace Idx

def elim0.{u} {α : Sort u} : Idx 0 → α
  | ⟨_, h⟩ => absurd h (Nat.not_lt_zero _)

variable {n : USize}

protected def ofUSize {n : USize} (a : USize) (h : n > 0) : Idx n :=
  ⟨a % n, sorry⟩

private theorem mlt {b : USize} : {a : USize} → a < n → b % n < n := sorry

-- shifting index with wrapping 
-- We want these operations to be invertible in `x` for every `y`. Is that the case?
-- Maybe we need to require that `n < USize.size/2`
@[default_instance]
instance {n} : HAdd (Idx n) USize (Idx n) := ⟨λ x y => ⟨(x.1 + y)%n, sorry⟩⟩
@[default_instance]
instance {n} : HSub (Idx n) USize (Idx n) := ⟨λ x y => ⟨((x.1 + n) - (y%n))%n, sorry⟩⟩
@[default_instance]
instance {n} : HMul USize (Idx n) (Idx n) := ⟨λ x y => ⟨(x * y.1)%n, sorry⟩⟩

def toFin {n} (i : Idx n) : Fin n.toNat := ⟨i.1.toNat, sorry⟩

instance {n} : Enumtype (Idx n) :=
{
  first := if h : 0 < n then some ⟨0, h⟩ else none
  next  := λ i =>
    if h : (i.1+1)<n then some ⟨i.1+1, h⟩ else none
  numOf   := n.toNat
  fromFin := λ i => ⟨i.1.toUSize, sorry⟩
  toFin   := λ i => i.toFin
  decEq := by infer_instance
  
  first_fromFin := sorry
  next_fromFin  := sorry
  next_toFin    := sorry
}

instance [Fact (n≠0)] : Nonempty (Idx n) := sorry

-- This does not work as intended :(
instance : OfNat (Idx (no_index (n+1))) i where
  ofNat := ⟨(i % (n+1).toNat).toUSize, sorry⟩
