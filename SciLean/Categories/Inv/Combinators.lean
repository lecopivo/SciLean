import SciLean.Std.Function
import SciLean.Categories.Inv.Core

open Function
namespace SciLean.Lin

variable {α β γ : Type}
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

-- id
instance : IsInv (id : α → α) := by simp[id] infer_instance

-- const
instance : IsInv (const _ : X → PUnit → X) := by simp[const]; infer_instance; done


#check Nat

instance (f : β → γ) (g : α → β) [IsInv f] [IsInv g] : IsInv (f ∘ g) := sorry
instance (f : β → γ) [IsInv f] : IsInv (λ (g : α → β) => f ∘ g) := sorry
instance (g : α → β) [IsInv g] : IsInv (λ (f : β → γ) => f ∘ g) := sorry

