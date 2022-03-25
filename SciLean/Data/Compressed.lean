import Mathlib
import SciLean.Quot.QuotQ

namespace SciLean

namespace Compressed

  -- β is the compressed type
  inductive Repr (α : Type) (β : Type) where
  | uncompr (a : α) : Repr α β
  | compr (b : β) : Repr α β

  namespace Repr

    variable {α β : Type}

    instance [Zero β] : Zero (Repr α β) := ⟨compr 0⟩
    instance [One β] : Zero (Repr α β) := ⟨compr 1⟩

    instance [Neg α] [Neg β] : Neg (Repr α β) := 
      ⟨λ x => 
        match x with
        | uncompr x => uncompr (-x)
        | compr   x => compr   (-x)⟩

    instance [HAdd γ α α] [HAdd γ β β] : HAdd γ (Repr α β) (Repr α β) := 
      ⟨λ c x => 
        match x with
        | uncompr x => uncompr (c + x)
        | compr   x => compr   (c + x)⟩

    instance [HMul γ α α] [HMul γ β β] : HMul γ (Repr α β) (Repr α β) := 
      ⟨λ c x => 
        match x with
        | uncompr x => uncompr (c * x)
        | compr   x => compr   (c * x)⟩

    instance [Add α] [Add β] [hadd1 : HAdd β α α] [hadd2 : HAdd α β α] : Add (Repr α β) := 
      ⟨λ x y => 
        match x, y with
        | uncompr x, uncompr y => uncompr (x + y)
        | compr   x, compr y   => compr   (x + y)
        | uncompr x, compr y   => uncompr (x + y)
        | compr   x, uncompr y => uncompr (x + y)⟩

    instance [Sub α] [Sub β] [hsub1 : HSub β α α] [hsub2 : HSub α β α] : Sub (Repr α β) := 
      ⟨λ x y => 
        match x, y with
        | uncompr x, uncompr y => uncompr (x - y)
        | compr   x, compr y   => compr   (x - y)
        | uncompr x, compr y   => uncompr (x - y)
        | compr   x, uncompr y => uncompr (x - y)⟩

    instance [Mul α] [Mul β] [hmul1 : HMul β α α] [hmul2 : HMul α β α] : Mul (Repr α β) := 
      ⟨λ x y => 
        match x, y with
        | uncompr x, uncompr y => uncompr (x * y)
        | compr   x, compr y   => compr   (x * y)
        | uncompr x, compr y   => uncompr (x * y)
        | compr   x, uncompr y => uncompr (x * y)⟩

    instance [Add α] : Add (Repr α Unit) := 
      ⟨λ x y => 
        match x, y with
        | uncompr x, uncompr y => uncompr (x + y)
        | compr   x, compr y   => compr   ()
        | uncompr x, compr y   => uncompr x
        | compr   x, uncompr y => uncompr y⟩

    instance [Sub α] [Neg α] : Sub (Repr α Unit) := 
      ⟨λ x y => 
        match x, y with
        | uncompr x, uncompr y => uncompr (x - y)
        | compr   x, compr y   => compr   ()
        | uncompr x, compr y   => uncompr x
        | compr   x, uncompr y => uncompr (-y)⟩

    instance [Mul α] : Mul (Repr α Unit) := 
      ⟨λ x y => 
        match x, y with
        | uncompr x, uncompr y => uncompr (x * y)
        | _        ,         _ => compr   ()⟩

    def Eq (eq : α → β → Prop) : Repr α β → Repr α β → Prop 
      | uncompr x, uncompr y => x = y
      | compr   x, compr   y => x = y
      | uncompr x, compr   y => eq x y
      | compr   x, uncompr y => eq y x

    open Quot'

    instance (eq : α → β → Prop) : QForm (Eq eq) where
      RedForm := λ lvl x => 
        match lvl with
        | redLvl _ => True
        | normLvl => 
          match x with 
          | compr _ => True
          | uncompr a => ∀ (b : β), ¬(eq a b)
      redform_norm := sorry
      redform_zero := sorry
      redform_succ := sorry
      redform_inf  := sorry
    
    instance (eq : α → β → Prop) (n : Nat) : QReduce (Eq eq) (redLvl n) where
      reduce := id
      is_reduce := sorry
      eq_reduce := sorry
      preserve_stronger := sorry

    -- ℝ^(n×m) := (ℝ^n)^m or (ℝ^m)^n ...

    instance [Zero α] [DecidableEq α] : QReduce (Eq (λ (a : α) (_ : Unit) => (a=0))) (normLvl) where
      reduce := λ x =>
        match x with
        | compr x => compr ()
        | uncompr x => if x=0 then compr () else uncompr x
      is_reduce := sorry
      eq_reduce := sorry
      preserve_stronger := sorry

    
  end Repr
      
end Compressed
