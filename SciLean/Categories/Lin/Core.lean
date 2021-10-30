import SciLean.Categories.Lin.Basic

namespace SciLean.Lin

variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]
variable {Y1 Y2 : Type} [Vec Y1] [Vec Y2]

instance identity : IsLin λ x : X => x := sorry
-- instance const (x : X) : IsLin λ y : Y => x := sorry
instance swap (f : α → Y → Z) [∀ a, IsLin (f a)] : IsLin (λ y a => f a y) := sorry
instance parm (f : X → β → Z) [IsLin f] (b : β) : IsLin (λ x => f x b) := sorry

instance diag (f : Y1 → Y2 → Z) (g1 : X → Y1) (g2 : X → Y2) [IsLin (λ yy : Y1 × Y2 => f yy.1 yy.2)] [IsLin g1] [IsLin g2] : IsLin (λ x => f (g1 x) (g2 x)) := sorry
instance comp (f : Y → Z) (g : X → Y) [IsLin f] [IsLin g] : IsLin (f ∘ g) := sorry
