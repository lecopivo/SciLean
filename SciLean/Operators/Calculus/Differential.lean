import SciLean.Operators.Calculus.Basic

namespace SciLean.Differential

variable {α β γ : Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]

instance (f : X → Y) [IsSmooth f] (x : X) : IsLin (δ f x) := sorry
-- TODO: Change IsSmooth to IsDiff
instance (f : X → Y) [IsSmooth f] : IsSmooth (δ f) := sorry

@[simp] 
theorem differential_of_linear (f : X → Y) [IsLin f] (x dx : X)
    : δ f x dx = f dx := sorry

@[simp] 
theorem differential_of_uncurried_linear_1 (f : X → Y → Z) [IsLin (λ xy : X×Y => f xy.1 xy.2)] 
    (x dx : X) (y : Y)
    : δ f x dx y = f dx 0 := sorry

@[simp] 
theorem differential_of_uncurried_linear_2 (f : X → Y → Z) [IsLin (λ xy : X×Y => f xy.1 xy.2)] 
    (x : X) (y dy : Y)
    : δ (f x) y dy = f 0 dy := sorry

@[simp] 
theorem differential_of_id (x dx : X)
    : δ (λ x => x) x dx = dx := by simp

@[simp] 
theorem differential_of_id'  (x dx : X)
    : δ (id) x dx = dx := by simp[id]

-- TODO: Change IsSmooth to IsDiff
@[simp] 
theorem differential_of_composition_1 (f : Y → Z) [IsSmooth f] (g : X → Y) [IsSmooth g] (x dx : X)
    : δ (λ x => f (g x)) x dx = δ f (g x) (δ g x dx) := sorry

-- TODO: Change IsSmooth to IsDiff
@[simp] 
theorem differential_of_composition_1_alt (f : Y → Z) [IsSmooth f] (g : X → Y) [IsSmooth g] (x dx : X)
    : δ (f∘g) x dx = δ f (g x) (δ g x dx) := by simp[Function.comp]

-- TODO: Change IsSmooth to IsDiff
@[simp] 
theorem differential_of_composition_2 (f : Y → Z) [IsSmooth f] (g dg : α → Y) (a : α)
    : δ (λ (g : α → Y) (a : α) => f (g a)) g dg a = δ f (g a) (dg a) := sorry

-- TODO: Change IsSmooth to IsDiff
@[simp] 
theorem differential_of_composition_3 (f df : β → Z) (g : α → β) (a : α)
    : δ (λ (f : β → Z) (g : α → β) (a : α) => f (g a)) f df g a = df (g a) := by simp
