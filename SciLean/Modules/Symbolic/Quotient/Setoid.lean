import SciLean.Prelude
import SciLean.Data.Quotient.Lattice
import SciLean.AutoImpl

/-- Function between Setoids
  Not sure about the name: Morphism, QFunction, QuotFun, QuotientFun, SetoidFun
  -/
class Setoid.Morphism {α : Type u} {β : Type v} [Setoid α] [Setoid β] (f : α → β) : Prop where
  is_sound : ∀ a a', a ≈ a' → f a ≈ f a'

class Setoid.Morphism₂ {α : Type u} {β : Type v} {γ : Type w} [Setoid α] [Setoid β] [Setoid γ] (f : α → β → γ) : Prop where
  is_sound : ∀ a a' b b', a ≈ a' → b ≈ b' → f a b ≈ f a' b'

class Setoid.Map {α : Type u} {β : Type v} [Setoid α] (f : α → β) : Prop where
  is_sound : ∀ a a', a ≈ a' → f a = f a'

noncomputable
def Quotient.repr {α : Type u} [inst : Setoid α] (a : Quotient inst) : α := Classical.choose a.exists_rep

namespace Setoid

  variable {α : Type u} [SA : Setoid α]
  variable {β : Type v} [SB : Setoid β]
  variable {γ : Type w} [SC : Setoid γ]

  instance id_is_mor : Morphism (λ x : α => x) where
    is_sound := by simp

  instance comp_is_mor (f : β → γ) [mf : Morphism f] (g : α → β) [mg : Morphism g]
    : Morphism (λ x => f (g x)) where
    is_sound :=
  by
    intros; apply mf.is_sound; apply mg.is_sound; assumption; done

  instance comp_is_map (f : β → δ) [mf : Map f] (g : α → β) [mg : Morphism g]
    : Map (λ x => f (g x)) where
    is_sound :=
  by
    intros; apply mf.is_sound; apply mg.is_sound; assumption; done

  instance scomb_is_mor (f : α → β → γ) [mf : Morphism₂ f] (g : α → β) [mg : Morphism g]
    : Morphism (λ x => f x (g x)) where
    is_sound :=
  by
    intros; apply mf.is_sound; assumption; apply mg.is_sound; assumption; done

  -- class QuotBracket {α : Type u} (a : α) (β : Type v) where
  --   quotBracket : β

  -- instance (α : Type u) [s : Setoid α] : QuotBracket α (β := Type u) where
  --   quotBracket := Quotient s

  -- instance {α} (a : α) [s : Setoid α] : QuotBracket a (Quotient s) where
  --   quotBracket := Quotient.mk _ a

  -- instance {α β} (f : α → β) [sa : Setoid α] [sb : Setoid β] [Morphism f] : QuotBracket f (Quotient sa → Quotient sb) where
  --   quotBracket := Quotient.lift (λ x : α => ⟦f x⟧) sorry_proof

  @[simp]
  theorem quotient_of_id (x : Quotient SA) : ⟦x.repr⟧ = x := sorry_proof   -- How do I prove this??

  @[simp]
  theorem quotient_of_morphism (f : α → β) [m : Morphism f] (x : α)
    : ⟦f x⟧ = Quotient.lift (λ x' => ⟦hold f x'⟧) (by intros; simp; apply Quot.sound; apply m.is_sound; sorry_proof /- wtf? this fails: assumption; done -/) ⟦x⟧
    := sorry_proof

  @[simp]
  theorem quotient_of_morphism₂ (f : α → β → γ) [m : Morphism₂ f] (x : α) (y : β)
    : ⟦f x y⟧ = Quotient.lift₂ (λ x' y' => ⟦hold f x' y'⟧) (by intros; simp; apply Quot.sound; apply m.is_sound; sorry_proof; sorry_proof) ⟦x⟧ ⟦y⟧
    := sorry_proof


  -- Should not be simp as it is variable head lhs :/
  theorem quotient_of_map (f : α → β) [m : Map f] (x : α)
    : f x = Quotient.lift (λ x' => hold f x') (by intros; simp; apply m.is_sound; sorry_proof) ⟦x⟧
    := sorry_proof


  section Operations

    -- variable {α : Type u} {β : Type v} {γ : Type w} [SA : Setoid α] [SB : Setoid β] [SC : Setoid γ]


    -- instance [HAdd α β γ] [Morphism₂ λ (x : α) (y : β) => x + y] : HAdd (Quotient SA) (Quotient SB) (Quotient SC)
    --   := ⟨λ x y => ⟦x.repr + y.repr⟧ rewrite_by simp⟩
    -- instance [HSub α β γ] [Morphism₂ λ (x : α) (y : β) => x - y] : HSub (Quotient SA) (Quotient SB) (Quotient SC)
    --   := ⟨λ x y => ⟦x.repr - y.repr⟧ rewrite_by simp⟩
    -- instance [HMul α β γ] [Morphism₂ λ (x : α) (y : β) => x * y] : HMul (Quotient SA) (Quotient SB) (Quotient SC)
    --   := ⟨λ x y => ⟦x.repr * y.repr⟧ rewrite_by simp⟩
    -- instance [HDiv α β γ] [Morphism₂ λ (x : α) (y : β) => x / y] : HDiv (Quotient SA) (Quotient SB) (Quotient SC)
    --   := ⟨λ x y => ⟦x.repr / y.repr⟧ rewrite_by simp⟩

    -- instance [Zero α] : One (Quotient SA) := ⟨⟦0⟧⟩
    -- instance [One α] : One (Quotient SA) := ⟨⟦1⟧⟩

  end Operations

end Setoid
