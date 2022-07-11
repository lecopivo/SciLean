import SciLean.Mathlib.Data.Enumtype
import SciLean.Core.Functions

namespace SciLean
structure Idx (n : Nat) where
  val : USize
  property : val < n.toUSize

def Idx.toFin {n} (i : Idx n) : Fin n := ⟨i.1.toNat, sorry⟩

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

instance Idx.HAdd.hAdd.arg_x.isInv (y : USize) : IsInv λ (x : Idx n) => x + y := sorry
instance Idx.HSub.hSub.arg_x.isInv (y : USize) : IsInv λ (x : Idx n) => x - y := sorry
@[simp] theorem Idx.HAdd.hAdd.arg_x.inv_simp [Nonempty (Idx n)] (y : USize) 
  : (λ (x : Idx n) => x + y)⁻¹ = λ (x : Idx n) => x - y := sorry
@[simp] theorem Idx.HSub.hSub.arg_x.inv_simp [Nonempty (Idx n)] (y : USize) 
  : (λ (x : Idx n) => x - y)⁻¹ = λ (x : Idx n) => x + y := sorry

instance : ToString (Idx n) := ⟨λ i => toString i.1⟩
