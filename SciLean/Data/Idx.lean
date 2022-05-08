import SciLean.Mathlib.Data.Enumtype
import SciLean.Core.Functions

namespace SciLean
structure Idx (n : USize) where
  val : USize
  property : val < n

def Idx.toFin {n} (i : Idx n) : Fin n.toNat := ⟨i.1.toNat, i.2⟩

-- instance (n) : Coe (Idx n) USize := ⟨λ x => x.1⟩

instance {n} : DecidableEq (Idx n) := 
  λ i j => if h : i.1=j.1 then isTrue sorry else isFalse sorry

instance {n} : Enumtype (Idx n) :=
{
  first := if n.1 ≠ ⟨0, by native_decide⟩ then some ⟨0, sorry⟩ else none
  next  := λ i =>
    if h : i.1+1<n then some ⟨i.1+1, h⟩ else none
  numOf   := n.toNat
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

instance {n} [Nonempty (Idx n)] : OfNat (Idx n) i := ⟨i.toUSize % n,sorry⟩

-- instance : Nonempty (Idx 1) := sorry
-- instance [Nonempty (Idx n)] : Nonempty (Idx (n+1)) := sorry

-- def i : Idx 14 := 0



-- instance {m} [Monad m] 
--          : ForIn m (Std.Range) USize :=
-- {
--   forIn := λ r init f => do
--         let mut val := init
--         for i in r do
--           match (← f i.toUSize val) with
--             | ForInStep.done val' => return val'
--             | ForInStep.yield val' => 
--               val ← pure val'
--         pure val
-- }

namespace Idx 
  inductive Range (n : USize)
  | all : Range n

  export Range (all)

end Idx

#check Idx.all

instance {m} [Monad m] {n}
         : ForIn m (Idx.Range (n:=n)) (Idx n) :=
{
  forIn := λ r init f => do
        let mut val := init
        for (i : Nat) in [0:n.toNat] do
          match (← f ⟨i.toUSize,sorry⟩ val) with
            | ForInStep.done val' => return val'
            | ForInStep.yield val' => 
              val ← pure val'
        pure val
}


