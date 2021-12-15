import SciLean.Std.Function
import SciLean.Categories.Lin.Basic

open Function
namespace SciLean.Lin

variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]
variable {Y1 Y2 : Type} [Vec Y1] [Vec Y2]

instance id_is_lin : IsLin λ x : X => x := sorry
instance const_zero_is_lin : IsLin (λ x : X => (0 : Y)) := sorry
instance (priority := low) swap_is_lin (f : α → Y → Z) [∀ a, IsLin (f a)] : IsLin (λ y a => f a y) := sorry
instance parm_is_lin (f : X → β → Z) [IsLin f] (b : β) : IsLin (λ x => f x b) := sorry

instance comp_is_lin (f : Y → Z) (g : X → Y) [IsLin f] [IsLin g] : IsLin (λ x => f (g x)) := sorry

instance diag_is_lin (f : Y1 → Y2 → Z) (g1 : X → Y1) (g2 : X → Y2) [IsLin (λ yy : Y1 × Y2 => f yy.1 yy.2)] [IsLin g1] [IsLin g2] : IsLin (λ x => f (g1 x) (g2 x)) := sorry
instance diag_parm_is_lin (f : Y1 → Y2 → Z) (g1 : X → α → Y1) (g2 : X → α → Y2) [IsLin (λ yy : Y1 × Y2 => f yy.1 yy.2)] [IsLin g1] [IsLin g2] : IsLin (λ x a => f (g1 x a) (g2 x a)) := sorry

-- uncurry variants of diag 
-- instance diag_uncurry_is_lin (f : Y1 → Y2 → Z) (g1 : X → Y1) (g2 : X → Y2) [IsLin (uncurry f)] [IsLin g1] [IsLin g2] : IsLin (λ x => f (g1 x) (g2 x)) := sorry
-- instance diag_parm_uncurry_is_lin (f : Y1 → Y2 → Z) (g1 : X → α → Y1) (g2 : X → α → Y2) [IsLin (uncurry f)] [IsLin g1] [IsLin g2] : IsLin (λ x a => f (g1 x a) (g2 x a)) := sorry
