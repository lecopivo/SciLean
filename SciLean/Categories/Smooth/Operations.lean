import SciLean.Categories.Smooth.Core

namespace SciLean.Smooth

variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

--- Arithmetic operations
instance : IsSmooth (λ x y : X => x + y) := sorry
instance (x : X) : IsSmooth (λ y : X => x + y) := sorry
instance : IsSmooth (λ x y : X => x - y) := sorry
instance (x : X) : IsSmooth (λ y : X => x - y) := sorry

instance : IsSmooth (λ (s : ℝ) (x : X) => s * x) := sorry
instance (s : ℝ) : IsSmooth (λ x : X => s * x) := sorry
