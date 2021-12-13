import SciLean.Categories.Smooth.Core

open Function
namespace SciLean.Smooth

variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

-- id
-- instance : IsSmooth (id : X → X) := by infer_instance

-- const
-- instance : IsSmooth (const β : X → β → X) := by infer_instance
instance (x : X) : IsSmooth (const Y x : Y → X) := by simp[const]; infer_instance

-- swap
-- instance : IsSmooth (swap : (α → β → Z) → (β → α → Z)) := by infer_instance 
-- instance (f : α → Y → Z) [∀ a, IsSmooth (f a)] : IsSmooth (swap f) := by infer_instance
-- instance (f : X → β → Z) (b : β) [IsSmooth f] : IsSmooth (swap f b) := by infer_instance

-- comp
-- instance : IsSmooth (comp : (β → Z) → (α → β) → (α → Z)) := by infer_instance  
instance (f : Y → Z) [IsSmooth f] : IsSmooth (comp f : (α → Y) → (α → Z)) := by simp[comp] infer_instance
instance (f : Y → Z) (g : X → Y) [IsSmooth f] [IsSmooth g] : IsSmooth (comp f g) := by simp[comp] infer_instance

