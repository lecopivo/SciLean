import SciLean.Operators.Calculus.DiffCore

namespace SciLean.Smooth

variable {α β γ : Type}
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]

set_option maxHeartbeats 900
set_option synthInstance.maxHeartbeats 200
set_option synthInstance.maxSize 50

--- Test 0 

-- I 
example : δ (λ x : X => x) = λ x dx => dx := by simp

-- K 
example : δ (λ (x : X) (y : Y) => x) = λ x dx y => dx := by simp
example (x : X) : δ (λ (y : Y) => x) = λ y dy => (0:X) := by simp

-- B
example 
  : δ (λ (f : Y → Z) (g : X → Y) (x : X) => f (g x)) 
    = 
    λ f df g x => df (g x) := by simp
example (f : Y → Z) [IsSmooth f] 
  : δ (λ (g : X → Y) (x : X) => f (g x)) 
    = 
    λ g dg x => δ f (g x) (dg x) := by simp
example (f : Y → Z) [IsSmooth f] 
  (g : X → Y) [IsSmooth g]
  : δ (λ (x : X) => f (g x)) 
    = 
    λ x dx => δ f (g x) (δ g x dx) := by simp

-- C
-- set_option trace.Meta.synthInstance true in
example 
  : δ (λ (f : X → Y → Z) (y : Y) (x : X) => f x y)
    =
    λ f df y x => df x y := by simp
example (f : X → Y → Z) [∀ x, IsSmooth (f x)]
  : δ (λ (y : Y) (x : X) => f x y)
    =
    λ y dy x => δ (f x) y dy := by simp 
example (f : X → Y → Z) [IsSmooth f] (y : Y)
  : δ (λ (x : X) => f x y)
    =
    λ x dx => δ f x dx y := by simp

-- S
example 
  : δ (λ (f : X → Y → Z) (g : X → Y) (x : X) => f x (g x))
    =
    λ f df g x => df x (g x) := by simp
example (f : X → Y → Z) [∀ x, IsSmooth (f x)]
  : δ (λ (g : X → Y) (x : X) => f x (g x))
    =
    λ g dg x => δ (f x) (g x) (dg x) := by simp
example (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)]
  (g : X → Y) [IsSmooth g]
  : δ (λ (x : X) => f x (g x))
    =
    λ x dx => δ f x dx (g x) + δ (f x) (g x) (δ g x dx) := by simp

-- diff_of_diag
example 
  (f : Y₁ → Y₂ → Z) [IsSmooth f] [∀ y₁, IsSmooth (f y₁)]
  (g₁ : X → Y₁) [IsSmooth g₁]
  (g₂ : X → Y₂) [IsSmooth g₂]
  : δ (λ x => f (g₁ x) (g₂ x)) 
    = 
    λ x dx => δ f (g₁ x) (δ g₁ x dx) (g₂ x) + 
              δ (f (g₁ x)) (g₂ x) (δ g₂ x dx) := by simp

-- diff_of_parm
example 
  (f : X → α → Y) [IsSmooth f]
  (a : α)
  : δ (λ x => f x a) = λ x dx => δ f x dx a := by simp
