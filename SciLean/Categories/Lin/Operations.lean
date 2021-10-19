import SciLean.Categories.Lin.Core

namespace SciLean.Lin

variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

--- Arithmetic operations
instance : IsLin (λ x : X×X => x.1+x.2) := sorry
instance : IsLin (λ x : X×X => x.1-x.2) := sorry
instance (r : ℝ) : IsLin (λ (x : X) => r*x) := sorry
instance (x : X) : IsLin (λ (r : ℝ) => r*x) := sorry
instance : IsLin (λ x : X => -x) := sorry

-- Basic operations with functions
instance (f : Y → Z) [IsLin f] (g : X → Y) [IsLin g] : IsLin (f ∘ g) := by simp[Function.comp] infer_instance done
