import SciLean.Operators.Calculus.Basic

namespace SciLean.Smooth

variable {α β γ : Type}
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]

----------------------------------------------------------------------

@[simp]
theorem diff_of_id
  : δ (λ x : X => x) = λ x dx => dx := sorry

@[simp]
theorem diff_of_const
  : δ (λ x : X => y) = λ x dx => (0 : Y) := sorry

@[simp low-3]
theorem diff_of_swap (f : α → X → Y) [∀ i, IsSmooth (f i)]
  : δ (λ x a => f a x) = λ x dx a => δ (f a) x dx := sorry

@[simp low-1]
theorem diff_of_comp
  (f : Y → Z) [IsSmooth f] 
  (g : X → Y) [IsSmooth g] 
  : δ (λ x => f (g x)) = λ x dx => δ f (g x) (δ g x dx) := sorry

@[simp low-2]
theorem diff_of_diag
  (f : Y₁ → Y₂ → Z) [IsSmooth f] [∀ y₁, IsSmooth (f y₁)]
  (g₁ : X → Y₁) [IsSmooth g₁]
  (g₂ : X → Y₂) [IsSmooth g₂]
  : δ (λ x => f (g₁ x) (g₂ x)) 
    = 
    λ x dx => δ f (g₁ x) (δ g₁ x dx) (g₂ x) + 
              δ (f (g₁ x)) (g₂ x) (δ g₂ x dx) := sorry

@[simp low]
theorem diff_of_parm
  (f : X → α → Y) [IsSmooth f]
  (a : α)
  : δ (λ x => f x a) = λ x dx => δ f x dx a := sorry

