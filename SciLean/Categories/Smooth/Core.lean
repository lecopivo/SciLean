import SciLean.Categories.Core
import SciLean.Categories.Smooth.Basic

namespace SciLean.Smooth

variable {α β γ δ ε ι : Type}
variable {β1 β2 β3 β4 : Type}
variable {X Y Z W U V : Type} [Vec X] [Vec Y] [Vec Z] [Vec W] [Vec U] [Vec V]
variable {Y1 Y2 Y3 Y4 : Type} [Vec Y1] [Vec Y2] [Vec Y3] [Vec Y4]
variable {E : ι → Type} {F : ι → Type} [∀ i, Vec (E i)] [∀ i, Vec (F i)]

-- ----- Cartesian Closedness of Convenient Vector Spaces
-- -- curry
-- instance (f : X × Y → Z) [IsSmooth f] : IsSmooth (curry f) := sorry
-- instance (f : X × Y → Z) (x : X) [IsSmooth f] : IsSmooth (curry f x) := sorry
-- -- uncurry
-- instance (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)] : IsSmooth (uncurry f) := sorry


-- -- fmap
-- instance fmap_is_smooth (f : (i : ι) → E i → F i) [∀ a, IsSmooth (f a)] : IsSmooth (fmap f) := sorry

instance identity : IsSmooth λ x : X => x := sorry
instance const (x : X) : IsSmooth λ y : Y => x := sorry
-- instance eval (g : α → β) : IsSmooth (λ (f : β → Z) (a : α) => f (g a)) := sorry
-- instance eval : IsSmooth (λ (f : α → Y) (a : α) => f a) := by infer_instance
instance swap (f : α → Y → Z) [∀ a, IsSmooth (f a)] : IsSmooth (λ y a => f a y) := sorry
instance parm (f : X → β → Z) [IsSmooth f] (b : β) : IsSmooth (λ x => f x b) := sorry

--- WARRNING: The order of these two instances is important ... I do not know why :(
instance diag (f : Y1 → Y2 → Z) (g1 : X → Y1) (g2 : X → Y2) [IsSmooth f] [∀ y1, IsSmooth (f y1)] : IsSmooth (λ x => f (g1 x) (g2 x)) := sorry
instance comp (f : Y → Z) (g : X → Y) [IsSmooth f] [IsSmooth g] : IsSmooth (f ∘ g) := sorry
