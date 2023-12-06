import Mathlib.Data.Fintype.Basic
import SciLean.Util.SorryProof
import SciLean.Data.Int64

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

protected def ofUSize {n : USize} (a : USize) (_ : n > 0) : Idx n :=
  ⟨a % n, sorry_proof⟩

private theorem mlt {b : USize} : {a : USize} → a < n → b % n < n := sorry_proof

-- shifting index with wrapping 
-- We want these operations to be invertible in `x` for every `y`. Is that the case?
-- Maybe we need to require that `n < USize.size/2`
@[default_instance]
instance : HAdd (Idx n) USize (Idx n) := ⟨λ x y => ⟨(x.1 + y)%n, sorry_proof⟩⟩
@[default_instance]
instance : HSub (Idx n) USize (Idx n) := ⟨λ x y => ⟨((x.1 + n) - (y + n))%n, sorry_proof⟩⟩
@[default_instance]
instance : HMul USize (Idx n) (Idx n) := ⟨λ x y => ⟨(x * y.1)%n, sorry_proof⟩⟩

@[default_instance]
instance : HAdd (Idx n) Int64 (Idx n) := ⟨λ x y => ⟨(x.1 + y.1 + n)%n, sorry_proof⟩⟩
@[default_instance]
instance : HSub (Idx n) Int64 (Idx n) := ⟨λ x y => ⟨(x.1 - (y.1 + n))%n, sorry_proof⟩⟩

@[default_instance]
instance : VAdd Int64 (Idx n) := ⟨λ x y => y + x⟩

def toFin {n} (i : Idx n) : Fin n.toNat := ⟨i.1.toNat, sorry_proof⟩
def toFin' {n : Nat} (i : Idx n.toUSize) : Fin n := ⟨i.1.toNat, sorry_proof⟩

@[extern c inline "(double)#1"]
def _root_.USize.toFloat (n : USize) : Float := n.toNat.toFloat
def toFloat {n} (i : Idx n) : Float := i.1.toFloat

@[macro_inline]
def cast (i : Idx n) (h : n = m) : Idx m := ⟨i.1, by rw[← h]; apply i.2⟩

@[macro_inline]
def cast' (i : Idx n) (h : m = n) : Idx m := ⟨i.1, by rw[h]; apply i.2⟩

def shiftPos (x : Idx n) (s : USize) := x + s
def shiftNeg (x : Idx n) (s : USize) := x - s
def shift (x : Idx n) (s : Int) := 
  match s with
  | .ofNat n => x.shiftPos n.toUSize
  | .negSucc n => x.shiftNeg (n+1).toUSize

/-- Splits index `i : Idx (n*m)` into `(i / n, i % n)`-/
def prodSplit (i : Idx (n*m)) : Idx n × Idx m := 
  (⟨i.1 / n, sorry_proof⟩, ⟨i.1 % n, sorry_proof⟩)

/-- Splits index `i : Idx (n*m)` into `(i / m, i % m)`-/
def prodSplit' (i : Idx (n*m)) : Idx m × Idx n := 
  (⟨i.1 % m, sorry_proof⟩, ⟨i.1 / m, sorry_proof⟩)
  
-- This does not work as intended :(

instance : OfNat (Idx (no_index (n+1))) i where
  ofNat := Idx.ofUSize i.toUSize sorry_proof

instance : Inhabited (Idx (no_index (n+1))) where
  default := 0

instance : Fintype (Idx n) where
  elems := {
      val := Id.run do
        let mut l : List (Idx n) := []
        for i in [0:n.toNat] do
          l := ⟨i.toUSize, sorry_proof⟩ :: l
        Multiset.ofList l.reverse
      nodup := sorry_proof
    }
  complete := sorry_proof


instance (n : Nat) : Nonempty (Idx (no_index (OfNat.ofNat (n+1)))) := sorry_proof
instance (n : Nat) : OfNat (Idx (no_index (OfNat.ofNat (n+1)))) i := ⟨(i % (n+1)).toUSize, sorry_proof⟩


end Idx

--------------------------------------------------------------------------------



/-- `Idx' a b = {x : Int64 // a ≤ x ∧ x ≤ b}`

WARRNING: Needs serious revision such that overflows are handled correctly!
-/
structure Idx' (a b : Int64) where
  val : Int64
  property : a ≤ val ∧ val ≤ b
  -- Maybe add this assumption then adding two `Idx n` won't cause overflow
  -- not_too_big : n < (USize.size/2).toUSize
deriving DecidableEq

instance : ToString (Idx' a b) := ⟨λ i => toString i.1⟩

instance {a b} : LT (Idx' a b) where
  lt a b := a.val < b.val

instance {a b} : LE (Idx' a b) where
  le a b := a.val ≤ b.val

namespace Idx'

variable {a b : Int64}

def toFloat (i : Idx' a b) : Float := i.1.toFloat
  
instance : Fintype (Idx n) where
  elems := {
      val := Id.run do
        let mut l : List (Idx n) := []
        for i in [0:n.toNat] do
          l := ⟨i.toUSize, sorry_proof⟩ :: l
        Multiset.ofList l.reverse
      nodup := sorry_proof
    }
  complete := sorry_proof

instance : Inhabited (Idx' (no_index (-a)) (no_index a)) where
  default := ⟨0, sorry_proof⟩
instance : Nonempty (Idx' (no_index (-a)) (no_index a)) := by infer_instance

