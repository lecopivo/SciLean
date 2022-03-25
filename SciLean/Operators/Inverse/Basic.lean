import SciLean.Categories


namespace SciLean


noncomputable
def inverse [n : Nonempty α] (f : α → β) (b : β)  : α :=
    match Classical.propDecidable (IsInv f) with
      | isTrue h => Classical.choose ((@IsInv.is_inv _ _ f h).2 b)
      | _ => Classical.choice n

postfix:max "⁻¹" => inverse


variable {α β γ : Type} [Nonempty α] [Nonempty β] [Nonempty γ]

@[simp]
def inverse_of_id
  : (λ a : α => a)⁻¹ = id := sorry

class Singleton (α : Type u) extends Inhabited α where
  unique : ∀ a b : α, a = b

@[simp low]
theorem inverse_of_swap 
  (f : α → β → γ) [∀ a, IsInv (f a)] [Singleton α]
  : (λ b a => f a b)⁻¹ = λ c => (f default)⁻¹ (c default) := sorry

@[simp]
theorem inverse_of_const [Singleton β]
  : (λ (a : α) (b : β) => a)⁻¹ = λ a => a default := by simp

@[simp] 
theorem inverse_of_comp
  (f : β → γ) [IsInv f]
  (g : α → β) [IsInv g]
  : (λ x => f (g x))⁻¹ = λ x => g⁻¹ (f⁻¹ x) := by sorry


