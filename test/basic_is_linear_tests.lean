import SciLean.Core.Functions

namespace SciLean.Lin.Tests

variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

namespace maintests

  variable {α β γ : Type}

  variable (f : Y → Z) (g : X → Y) [IsLin f] [IsLin g] (h : X → X) [IsLin h] (h' : Y → Y) [IsLin h']
  variable (F : Y → α → X) [IsLin F]
  variable (G : X → α → β → Y) [IsLin G]
  variable (H : α → X → β → Y) [∀ a, IsLin (H a)]
  variable (H': α → β → X → Y) [∀ a b, IsLin (H' a b)]

  example : IsLin (λ x => g x) := by infer_instance
  example : IsLin (λ x => f (g x)) := by infer_instance
  example : IsLin (λ x => f (g (h (h x)))) := by infer_instance
  example : IsLin (λ (g' : X → Y) => f ∘ g') := by infer_instance
  example : IsLin (λ (x : X) => F (g (h x)) a) := by infer_instance
  example : IsLin (λ (x : X) => h (F (h' ((h' ∘ g) (h x))) a)) := by simp; infer_instance
  example : IsLin (f ∘ g) := by simp; infer_instance
  example : IsLin (λ (x : X) => G (h x) a b) := by infer_instance
  example : IsLin (λ (x : X) => H a (h x) b) := by infer_instance
  example : IsLin (λ (x : X) => H' a b (h x)) := by infer_instance
  example (f : X → X → Y) [IsLin (λ xx : X×X => f xx.1 xx.2)] : IsLin (λ x => f x x) := by infer_instance
  example (f : X → X → Y) [IsLin (λ xx : X×X => f xx.1 xx.2)] : IsLin (λ x => f (h x) x) := by infer_instance
  example (f : X → X → Y) [IsLin (λ xx : X×X => f xx.1 xx.2)] : IsLin (λ x => f x (h x)) := by infer_instance

  -- set_option synthInstance.maxHeartbeats 5000
  example : IsLin (λ (f : Y → Z) (x : X) => (f (g x))) := by infer_instance
  example : IsLin (λ (h'' : X → X) (x : X) => (h (h'' ((h ∘ h) x)))) := by infer_instance
  example : IsLin (λ (h'' : X → X) (x : X) => (h ∘ h ∘ h) (h (h'' (h ((h ∘ h) x))))) := by infer_instance
  example : IsLin (λ (g : X → Y) (x : X) => F (g (h x)) a) := by infer_instance
  example : IsLin (λ (h : X → X) (x : X) => H a (h x) b) := by infer_instance
  example (f : β → Y → Z) [∀ b, IsLin (f b)] : IsLin (λ (g : α → Y) (b : β) (a : α) => f b (g a)) := by infer_instance
  example : IsLin (λ (h : X → X) (x : X) => H' a b (h x)) := by infer_instance
  example (f : X → X → α → Y) [∀ a, IsLin (λ xx : X×X => f xx.1 xx.2 a)] (a : α) : IsLin (λ x => f (h x) x a) := by infer_instance
  example : IsLin (λ (h : X → X) (x : X) => G (h x) a b) := by infer_instance
  -- set_option synthInstance.maxHeartbeats 500

  -- example (f : X → α → X → Y) (a : α) [IsLin (λ xx : X×X => f xx.1 a xx.2)] : IsLin (λ x => f x a x) := by infer_instance
  -- example (f : X → α → X → Y) (a : α) [IsLin (λ xx : X×X => f xx.1 a xx.2)] : IsLin (λ x => f (h x) a x) := by infer_instance
  -- example (f : X → α → X → Y) (a : α) [IsLin (λ xx : X×X => f xx.1 a xx.2)] : IsLin (λ x => f x a (h x)) := by infer_instance
  -- example (f : X → α → X → Y) (a : α) [IsLin (λ xx : X×X => f xx.1 a xx.2)] : IsLin (λ x => f (h x) a (h x)) := by infer_instance
  -- example (f : X → α → X → Y) (a : α) [IsLin (λ xx : X×X => f xx.1 a xx.2)] : IsLin (λ (h : X → X) x => f (h x) a (h x)) := by infer_instance

  -- set_option trace.Meta.synthInstance true
  -- example (f : X → Y → Z) (y : Y) [IsLin (λ xy : X×Y => f xy.1 xy.2)] : IsLin (λ x => f x y) := by infer_instance
  -- set_option trace.Meta.synthInstance false

end maintests

namespace combtests
variable {α β γ : Type} 
variable {X : Type} {Y : Type} {Z : Type} [Vec X] [Vec Y] [Vec Z]

example (f : X → X) [IsLin f] : IsLin ((f ∘ f) ∘ (f ∘ (f ∘ f))) := by infer_instance
example (y : X) (A : X → X) (B : X → X) [IsLin A] [IsLin B] : IsLin λ x => (B∘A) x + B (A (B x) + B x) := by infer_instance


section multilinear_test

abbrev f (xy : ℝ × ℝ) (z : ℝ) := z * (xy.1 + xy.2)

example (xy) : IsLin λ z  => f xy z := by infer_instance
example (z)  : IsLin λ xy => f xy z := by infer_instance

end multilinear_test

 
end combtests

