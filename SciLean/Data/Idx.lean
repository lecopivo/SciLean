import SciLean.Mathlib.Data.Enumtype
-- import SciLean.Core.Functions

namespace SciLean

structure Idx (n : USize) where
  val : USize
  property : val < n
deriving DecidableEq

class Index (ι : Type u) extends Iterable ι where
  numOf : USize
  fromIdx : Idx numOf → ι
  toIdx : ι → Idx numOf
  
  fromIdx_toIdx : fromIdx ∘ toIdx = id
  toIdx_fromIdx : toIdx ∘ fromIdx = id

def Idx.toFin {n} (i : Idx n) : Fin n.toNat := ⟨i.1.toNat, sorry⟩

instance : Index (Idx n) where
  first := if h : 0 < n then some ⟨0,h⟩ else none
  next := λ i => if h : i.1 + 1 < n then some ⟨i.1 + 1, h⟩ else none
  decEq := by infer_instance

  numOf := n
  fromIdx := id
  toIdx := id
  
  fromIdx_toIdx := by simp
  toIdx_fromIdx := by simp

-- instance [Index ι] [Index κ] : Index (ι×κ) where
--   numOf := if (Index.numOf ι).toNat * (Index.numOf κ).toNat < USize.max then Index.numOf ι * Index.numOf κ else panic! "asdf"

instance {n} : DecidableEq (Idx n) := 
  λ i j => if h : i.1=j.1 then isTrue sorry else isFalse sorry

instance {n} : Enumtype (Idx n) :=
{
  first := if n ≠ 0 then some ⟨0, sorry⟩ else none
  next  := λ i =>
    if h : (i.1+1)<n then some ⟨i.1+1, h⟩ else none
  numOf   := n
  fromFin := λ i => ⟨i.1.toUSize, sorry⟩
  toFin   := λ i => i.toFin
  decEq := by infer_instance
  
  first_fromFin := sorry
  next_fromFin  := sorry
  next_toFin    := sorry
}

instance [Fact (n≠0)] : Nonempty (Idx n) := sorry

instance {n} : HAdd (Idx n) USize (Idx n) := ⟨λ x y => ⟨(x.1 + y)%n, sorry⟩⟩
instance {n} : HSub (Idx n) USize (Idx n) := ⟨λ x y => ⟨(x.1 + n - (y%n))%n, sorry⟩⟩


instance : ToString (Idx n) := ⟨λ i => toString i.1⟩
