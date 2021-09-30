import SciLean.Prelude

variable {α β γ : Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]

instance : IsZero (0 : X) := by constructor; rfl
instance (x y : X) [IsZero x] [IsZero y] : IsZero (x + y) := sorry
instance (x y : X) [IsZero x] [IsZero y] : IsZero (x - y) := sorry
instance (x : X)  : IsZero (x - x) := sorry
instance (f : α → X) [∀ a, IsZero (f a)] : IsZero f := sorry
instance (x : X) (y : Y) [IsZero x] [IsZero y] : IsZero (x,y) := sorry
instance (f : X → Y) [IsLin f] [IsZero x] : IsZero (f x) := sorry
instance (f : X → Y) [IsAff f] [IsZero x] : IsZero (f x - f 0) := sorry
instance (f : X → Y) [IsAff f] [IsZero x] : IsZero (f 0 - f x) := sorry
