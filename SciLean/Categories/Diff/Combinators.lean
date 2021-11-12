import SciLean.Categories.Diff.Basic

namespace SciLean.Smooth

variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

-- id
instance : IsDiff (id : X → X) := by infer_instance

-- const
instance : IsDiff (const β : X → β → X) := by infer_instance
instance (x : X) : IsDiff (const Y x : Y → X) := by infer_instance 

-- swap
instance : IsDiff (swap : (α → β → Z) → (β → α → Z)) := by infer_instance 
instance (f : α → Y → Z) [∀ a, IsDiff (f a)] : IsDiff (swap f) := sorry
instance (f : X → β → Z) (b : β) [IsDiff f] : IsDiff (swap f b) := sorry

-- comp
instance : IsDiff (comp : (β → Z) → (α → β) → (α → Z)) := by infer_instance 
instance (f : Y → Z) [IsDiff f] : IsDiff (comp f : (α → Y) → (α → Z)) := sorry
instance (f : Y → Z) (g : X → Y) [IsDiff f] [IsDiff g] : IsDiff (comp f g) := sorry

-- What is the role of these????
instance (f : Y → α → Z) (g : X → Y) (a : α) [IsDiff g] [IsDiff (swap f a)] 
         : IsDiff (swap (comp f g) a) := sorry
instance (f : β → Y → Z) [∀ b, IsDiff (f b)] 
         : IsDiff ((swap (comp comp (swap comp)) f) : (α → Y) → β → (α → Z)) := sorry

-- diag
instance : IsDiff (@diag α Y) := by infer_instance 
instance (f : X → X → Y) [IsDiff f] [∀ x, IsDiff (f x)] : IsDiff (diag f) := sorry
