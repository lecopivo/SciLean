import SciLean.Categories.Cont.Basic

namespace SciLean.Cont

variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

-- id
instance : IsCont (id : X → X) := by infer_instance

-- const
instance : IsCont (const β : X → β → X) := by infer_instance
instance (x : X) : IsCont (const Y x : Y → X) := by infer_instance

-- swap
instance : IsCont (swap : (α → β → Z) → (β → α → Z)) := by infer_instance
instance (f : α → Y → Z) [∀ a, IsCont (f a)] : IsCont (swap f) := sorry
instance (f : X → β → Z) (b : β) [IsCont f] : IsCont (swap f b) := sorry

-- comp
instance : IsCont (comp : (β → Z) → (α → β) → (α → Z)) := by infer_instance 
instance (f : Y → Z) [IsCont f] : IsCont (comp f : (α → Y) → (α → Z)) := sorry
instance (f : Y → Z) (g : X → Y) [IsCont f] [IsCont g] : IsCont (comp f g) := sorry

-- What is the role of these????
instance (f : Y → α → Z) (g : X → Y) (a : α) [IsCont g] [IsCont (swap f a)] 
         : IsCont (swap (comp f g) a) := sorry
instance (f : β → Y → Z) [∀ b, IsCont (f b)] 
         : IsCont ((swap (comp comp (swap comp)) f) : (α → Y) → β → (α → Z)) := sorry

-- diag
instance : IsCont (@diag α Y) := by infer_instance 
instance (f : X → X → Y) [IsCont f] [∀ x, IsCont (f x)] : IsCont (diag f) := sorry
