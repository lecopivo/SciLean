import SciLean.Std.Function
import SciLean.Categories.Smooth.Basic

open Function
namespace SciLean.Smooth

variable {α β γ δ ε ι : Type}
variable {β1 β2 β3 β4 : Type}
variable {X Y Z W U V : Type} [Vec X] [Vec Y] [Vec Z] [Vec W] [Vec U] [Vec V]
variable {Y1 Y2 Y3 Y4 : Type} [Vec Y1] [Vec Y2] [Vec Y3] [Vec Y4]
variable {E : ι → Type} {F : ι → Type} [∀ i, Vec (E i)] [∀ i, Vec (F i)]

----- Cartesian Closedness of Convenient Vector Spaces
-- curry
instance (f : X × Y → Z) [IsSmooth f] : IsSmooth (curry f) := sorry
instance (f : X × Y → Z) (x : X) [IsSmooth f] : IsSmooth (curry f x) := sorry
-- uncurry
instance (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)] : IsSmooth (uncurry f) := sorry

-- fmap
-- instance fmap_is_smooth (f : (i : ι) → E i → F i) [∀ a, IsSmooth (f a)] : IsSmooth (fmap f) := sorry

instance id_is_smooth : IsSmooth λ x : X => x := sorry
instance const_is_smooth (x : X) : IsSmooth λ y : Y => x := sorry
instance swap_is_smooth (f : α → Y → Z) [∀ a, IsSmooth (f a)] : IsSmooth (λ y a => f a y) := sorry
instance parm_is_smooth (f : X → β → Z) [IsSmooth f] (b : β) : IsSmooth (λ x => f x b) := sorry
instance comp_is_smooth (f : Y → Z) (g : X → Y) [IsSmooth f] [IsSmooth g] : IsSmooth (λ x => f (g x)) := sorry
instance diag_is_smooth (f : Y1 → Y2 → Z) (g1 : X → Y1) (g2 : X → Y2) [IsSmooth f] [∀ y1, IsSmooth (f y1)] : IsSmooth (λ x => f (g1 x) (g2 x)) := sorry
