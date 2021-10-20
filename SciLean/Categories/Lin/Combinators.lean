import SciLean.Categories.Lin.Basic

namespace SciLean.Lin

variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

-- id
instance : IsLin (id : X → X) := sorry

-- const
instance : IsLin (const β : X → β → X) := sorry
instance : IsLin (const Y (0 : X) : Y → X) := sorry

-- swap
instance : IsLin (@swap α β Z) := sorry
instance (f : α → Y → Z) [∀ a, IsLin (f a)] : IsLin (swap f) := sorry
instance (f : X → β → Z) (b : β) [IsLin f] : IsLin (swap f b) := sorry

-- comp
instance : IsLin (@comp α β Z) := sorry
instance (f : Y → Z) [IsLin f] : IsLin (@comp α _ _ f) := sorry
instance (f : Y → Z) (g : X → Y) [IsLin f] [IsLin g] : IsLin (comp f g) := sorry

-- What is the role of these????
instance (f : Y → α → Z) (g : X → Y) (a : α) [IsLin g] [IsLin (swap f a)] 
         : IsLin (swap (comp f g) a) := sorry
instance (f : β → Y → Z) [∀ b, IsLin (f b)] 
         : IsLin ((swap (comp comp (swap comp)) f) : (α → Y) → β → (α → Z)) := sorry

-- diag
instance : IsLin (@diag α Y) := sorry

-- is asking for [IsLin (uncurry f)] safe ? Or will it cause infinite loop?
instance (f : X → X → Y) [IsLin (uncurry f)] : IsLin (diag f) := sorry
instance (g : X → Y) [IsLin g] (f : Y → X → Z) [IsLin (uncurry f)] : IsLin (diag (comp f g) : X → Z) := sorry
instance (g : X → Y) [IsLin g] (f : X → Y → Z) [IsLin (uncurry f)] : IsLin (diag (comp (swap comp g) f) : X → Z) := sorry
--- Is this one necessary ? Maybe the previous two will peel of first fun and then the second one...
instance (h g : X → Y) [IsLin h] [IsLin g] (f : Y → Y → Z) [IsLin (uncurry f)] : IsLin (diag (comp (swap comp h) (comp f g)) : X → Z) := sorry



