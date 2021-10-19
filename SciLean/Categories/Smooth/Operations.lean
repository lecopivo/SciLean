import SciLean.Categories.Smooth.Core

namespace SciLean.Smooth

variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

--- Arithmetic operations
instance : IsSmooth (λ x y : X => x + y) := sorry
instance : IsSmooth (λ y x : X => y + x) := sorry
instance : IsSmooth (λ x y : X => x - y) := sorry
instance : IsSmooth (λ y x : X => y - x) := sorry

-- Basic operations with functions
instance (f : Y → Z) [IsSmooth f] (g : X → Y) [IsSmooth g] : IsSmooth (f ∘ g) := by simp[Function.comp] infer_instance done
