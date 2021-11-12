import SciLean.Categories.Smooth.Basic

namespace SciLean.Smooth

variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

-- id
instance : IsSmooth (id : X → X) := by infer_instance

-- const
instance : IsSmooth (const β : X → β → X) := by infer_instance
instance (x : X) : IsSmooth (const Y x : Y → X) := sorry

-- swap
instance : IsSmooth (swap : (α → β → Z) → (β → α → Z)) := by infer_instance 
instance (f : α → Y → Z) [∀ a, IsSmooth (f a)] : IsSmooth (swap f) := sorry
instance (f : X → β → Z) (b : β) [IsSmooth f] : IsSmooth (swap f b) := sorry

-- comp
instance : IsSmooth (comp : (β → Z) → (α → β) → (α → Z)) := by infer_instance  
instance (f : Y → Z) [IsSmooth f] : IsSmooth (comp f : (α → Y) → (α → Z)) := sorry
instance (f : Y → Z) (g : X → Y) [IsSmooth f] [IsSmooth g] : IsSmooth (comp f g) := sorry

-- What is the role of these????
instance (f : Y → α → Z) (g : X → Y) (a : α) [IsSmooth g] [IsSmooth (swap f a)] 
         : IsSmooth (swap (comp f g) a) := sorry
instance (f : β → Y → Z) [∀ b, IsSmooth (f b)] 
         : IsSmooth ((swap (comp comp (swap comp)) f) : (α → Y) → β → (α → Z)) := sorry

-- diag
instance : IsSmooth (@diag α Y) := by infer_instance 
instance (f : X → X → Y) [IsSmooth f] [∀ x, IsSmooth (f x)] : IsSmooth (diag f) := sorry
