import SciLean.Categories.Inv.Basic

namespace SciLean.Inv

variable {α β γ}
variable {β1 β2}

instance : IsInv (λ a : α => a) := sorry
instance : IsInv (λ (a : α) (p : PUnit) => a) := sorry  -- Generalize to any singleton type
instance (f : β → γ) (g : α → β) [IsInv f] [IsInv g] : IsInv (λ x => f (g x)) := sorry
instance (f : β1 → β2 → γ) (g1 : α → β1) (b2 : β2) [IsInv (λ b1 => f b1 b2)] [IsInv g1] : IsInv (λ a => f (g1 a) b2) := sorry
instance (f : β1 → β2 → γ) (g2 : α → β2) (b1 : β1) [IsInv (λ b2 => f b1 b2)] [IsInv g2] : IsInv (λ a => f b1 (g2 a)) := sorry
