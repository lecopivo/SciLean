import SciLean.Operators.Adjoint.alt.Operations

open SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
variable {Y₁ Y₂ : Type} [SemiHilbert Y₁] [SemiHilbert Y₂]
variable {ι κ} [Enumtype ι] [Enumtype κ]

-------------------------------------------------------

example
  : HasAdjoint λ x : X => x := by infer_instance

example
  : HasAdjoint (λ (x : X) (i : ι) => x) := by infer_instance

example
  (f : ι → Y → Z) [∀ i, HasAdjoint (f i)] 
  : HasAdjoint (λ y a => f a y) := by infer_instance

example
  (f : Y → Z) [HasAdjoint f] 
  (g : X → Y) [HasAdjoint g] 
  : 
    HasAdjoint (λ x => f (g x)) := by infer_instance

example
  (f : Y₁ → Y₂ → Z) [HasAdjoint (λ yy : Y₁ × Y₂ => f yy.1 yy.2)] 
  (g₁ : X → Y₁) [HasAdjoint g₁] 
  (g₂ : X → Y₂) [HasAdjoint g₂] 
  : HasAdjoint (λ x => f (g₁ x) (g₂ x)) := by infer_instance

example
  (f : X → ι → Z) [HasAdjoint f] 
  (i : ι) 
  : HasAdjoint (λ x => f x i) := by infer_instance

example
  (b : β) 
  (f : Y → β → Z) [HasAdjoint (λ y => f y b)]
  (g : X → Y) [HasAdjoint g] 
  : HasAdjoint (λ x => f (g x) b) := by infer_instance

example
  (a : α) (b : β) 
  (f : Y → α → β → Z) [HasAdjoint (λ y => f y a b)]
  (g : X → Y) [HasAdjoint g] 
  : HasAdjoint (λ x => f (g x) a b) := by infer_instance

example
  (a : α) (b : β) 
  (f : Y → β → Z) [HasAdjoint (λ y => f y b)]
  (g : X → α → Y) [HasAdjoint (λ x => g x a)] 
  : HasAdjoint (λ x => f (g x a) b) := by infer_instance

example 
  (a : α) (b : β) (c : γ)
  (f : Y → α → β → γ → Z) [HasAdjoint (λ y => f y a b c)]
  (g : X → Y) [HasAdjoint g] 
  : HasAdjoint (λ x => f (g x) a b c) := by infer_instance

example
  (a : α) (b : β) 
  (f : α → Y → β → Z) [HasAdjoint (λ y => f a y b)]
  (g : X → Y) [HasAdjoint g] 
  : HasAdjoint (λ x => f a (g x) b) := by infer_instance

example 
  (a : α) (b : β) (c : γ)
  (f : Y₁ → Y₂ → γ → Z) [HasAdjoint (λ yy : Y₁ × Y₂ => f yy.1 yy.2 c)] 
  (g₁ : X → α → β → Y₁) [HasAdjoint (λ x => g₁ x a b)] 
  (g₂ : X → β → Y₂) [HasAdjoint (λ x => g₂ x b)] 
  : HasAdjoint (λ x => f (g₁ x a b) (g₂ x b) c) := by infer_instance

example 
  : HasAdjoint (λ p : X×Y => p.1) := by infer_instance
example 
  : HasAdjoint (λ p : X×Y => p.2) := by infer_instance

--------------------------

example
  : (λ x : X => x)† = λ x => x := by simp

example
  : (λ (x : X) (i : ι) => x)† = λ f => ∑ i, f i := by simp

example
  (f : ι → Y → Z) [∀ i, HasAdjoint (f i)] 
  : (λ y i => f i y)† = λ g => ∑ i, (f i)† (g i) := by simp

example
  (f : Y → Z) [HasAdjoint f] 
  (g : X → Y) [HasAdjoint g] 
  : (λ x => f (g x))† = λ z => g† (f† z) := by simp

example 
  (f : Y₁ → Y₂ → Z) [HasAdjoint (λ yy : Y₁ × Y₂ => f yy.1 yy.2)] 
  (g₁ : X → Y₁) [HasAdjoint g₁] 
  (g₂ : X → Y₂) [HasAdjoint g₂] 
  : (λ x => f (g₁ x) (g₂ x))† 
    = 
    λ z => (λ (y₁,y₂) => (g₁† y₁) + (g₂† y₂)) $ 
           (λ (y₁,y₂) => f y₁ y₂)† z 
:= by simp done

example 
  (f : X → ι → Z) [HasAdjoint f]
  (i : ι)
  : (λ x => f x i)† = (λ z => f† (λ j => (kron i j) * z)) 
:= by simp 

example 
  [Nonempty ι]
  (h : ι → κ) [IsInv h] 
  : (λ (f : κ → X) (i : ι) => f (h i))† 
    = 
    λ (g : ι → X) (j : κ) => g (h⁻¹ j) 
:= by simp

example
  [Nonempty ι]
  (f : ι → X → Y) [∀ i, HasAdjoint (f i)] 
  (h : ι → κ) [IsInv h]
  : (λ (x : κ → X) i => f i (x (h i)))† 
    = 
    (λ y j => (f (h⁻¹ j))† (y (h⁻¹ j)))
:= by simp 

example
  : (λ ((x, y) : X×Y) => x)† = λ x => (x, (0 : Y)) := by simp

example
  : (λ ((x, y) : X×Y) => y)† = λ y => ((0 : X), y) := by simp

example
  : (λ ((x, y) : X×Y) => (y,x))† = λ (y,x) => (x, y) := by simp 

-- almost done, but `2 * 0` does not simplify to `0`
-- example
--   : (λ ((x, y) : X×Y) => (x,x))† = λ (x,x') => (x + x', (0 : Y)) := by simp
