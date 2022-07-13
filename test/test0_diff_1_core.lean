import SciLean.Core.Functions
-- import SciLean.Tactic.AutoDiff.Main
-- import SciLean.Tactic.CustomSimp.DebugSimp

namespace SciLean.Smooth

variable {α β γ : Type}
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]

set_option maxHeartbeats 900
set_option synthInstance.maxHeartbeats 200
set_option synthInstance.maxSize 50

--- Test 0 

-- We want to solve all these in a single pass i.e. linear complexity in the expression size
macro "diff_simp" : tactic => `(simp) -- `(autodiff_core (config := {singlePass := true}))

-- I 
example : ∂ (λ x : X => x) = λ x dx => dx := by diff_simp

-- K 
example : ∂ (λ (x : X) (y : Y) => x) = λ x dx y => dx := by diff_simp
example (x : X) : ∂ (λ (y : Y) => x) = λ y dy => (0:X) := by diff_simp

-- B
example 
  : ∂ (λ (f : Y → Z) (g : X → Y) (x : X) => f (g x)) 
    = 
    λ f df g x => df (g x) := by diff_simp
example (f : Y → Z) [IsSmooth f] 
  : ∂ (λ (g : X → Y) (x : X) => f (g x)) 
    = 
    λ g dg x => ∂ f (g x) (dg x) := by diff_simp
example (f : Y → Z) [IsSmooth f] 
  (g : X → Y) [IsSmooth g]
  : ∂ (λ (x : X) => f (g x)) 
    = 
    λ x dx => ∂ f (g x) (∂ g x dx) := by diff_simp

-- C
-- set_option trace.Meta.synthInstance true in
set_option trace.Meta.Tactic.simp true in
set_option trace.Meta.Tactic.simp.unify false in
example 
  : ∂ (λ (f : X → Y → Z) (y : Y) (x : X) => f x y)
    =
    λ f df y x => df x y := by diff_simp
example (f : X → Y → Z) [∀ x, IsSmooth (f x)]
  : ∂ (λ (y : Y) (x : X) => f x y)
    =
    λ y dy x => ∂ (f x) y dy := by diff_simp 
example (f : X → Y → Z) [IsSmooth f] (y : Y)
  : ∂ (λ (x : X) => f x y)
    =
    λ x dx => ∂ f x dx y := by diff_simp

-- S
-- set_option trace.Meta.Tactic.simp true in
example 
  : ∂ (λ (f : X → Y → Z) (g : X → Y) (x : X) => f x (g x))
    =
    λ f df g x => df x (g x) := by diff_simp
example (f : X → Y → Z) [∀ x, IsSmooth (f x)]
  : ∂ (λ (g : X → Y) (x : X) => f x (g x))
    =
    λ g dg x => ∂ (f x) (g x) (dg x) := by diff_simp
example (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)]
  (g : X → Y) [IsSmooth g]
  : ∂ (λ (x : X) => f x (g x))
    =
    λ x dx => ∂ f x dx (g x) + ∂ (f x) (g x) (∂ g x dx) := by diff_simp

-- diff_of_diag
example 
  (f : Y₁ → Y₂ → Z) [IsSmooth f] [∀ y₁, IsSmooth (f y₁)]
  (g₁ : X → Y₁) [IsSmooth g₁]
  (g₂ : X → Y₂) [IsSmooth g₂]
  : ∂ (λ x => f (g₁ x) (g₂ x)) 
    = 
    λ x dx => ∂ f (g₁ x) (∂ g₁ x dx) (g₂ x) + 
              ∂ (f (g₁ x)) (g₂ x) (∂ g₂ x dx) := by diff_simp

-- diff_of_parm
example 
  (f : X → α → Y) [IsSmooth f]
  (a : α)
  : ∂ (λ x => f x a) = λ x dx => ∂ f x dx a := by diff_simp
