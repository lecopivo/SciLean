import SciLean.Core

open SciLean

variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

namespace maintests

  variable {α β γ : Type}

  variable (f : Y → Z) (g : X → Y) [IsSmoothT f] [IsSmoothT g] (h : X → X) [IsSmoothT h] (h' : Y → Y) [IsSmoothT h']
  variable (a : α) (b : β)
  variable (F : Y → α → X) [IsSmoothT F]
  variable (G : X → α → β → Y) [IsSmoothT G]
  variable (G' : X → Z → W → Y) (z : Z) (w : W) [IsSmoothT G']
  variable (H : α → X → β → Y) [IsSmoothT (H a)]
  variable (H': α → β → X → Y) [IsSmoothT (H' a b)]

  example : IsSmoothT (λ x => g x) := by infer_instance
  example : IsSmoothT (λ x => f (g x)) := by infer_instance
  example : IsSmoothT (λ x => f (g (h (h x)))) := by infer_instance
  example : IsSmoothT (λ (g' : X → Y) => f ∘ g') := by unfold Function.comp; infer_instance
  example : IsSmoothT (λ (x : X) => F (g (h x)) a) := by infer_instance
  example : IsSmoothT (f ∘ g) := by unfold Function.comp; infer_instance
  example : IsSmoothT (λ (f : Y → Z) (x : X) => (f (g x))) := by infer_instance
  example : IsSmoothT (λ (h'' : X → X) (x : X) => h (h (h (h'' ((h ∘ h) (h x)))))) := by infer_instance
  example : IsSmoothT (λ (x : X) => G (h x) a b) := by infer_instance
  example : IsSmoothT (λ (x : X) => H a (h x) b) := by infer_instance
  example : IsSmoothT (λ (x : X) => H' a b (h x)) := by infer_instance
  example (f : β → Y → Z) [∀ b, IsSmoothT (f b)] : IsSmoothT (λ (g : α → Y) (b : β) (a : α) => f b (g a)) := by infer_instance
  example (f : X → X → Y) [∀ x, IsSmoothT (f x)] [IsSmoothT λ x => λ y ⟿ f x y]: IsSmoothT (λ x => f x x) := by infer_instance
  example (f : X → X → Y) [∀ x, IsSmoothT (f x)] [IsSmoothT λ x => λ y ⟿ f x y] : IsSmoothT (λ x => f (h x) x) := by infer_instance
  example (f : X → X → Y) [∀ x, IsSmoothT (f x)] [IsSmoothT λ x => λ y ⟿ f x y] : IsSmoothT (λ x => f x (h x)) := by infer_instance
  example : IsSmoothT (λ (h : X → X) (x : X) => H' a b (h x)) := by infer_instance
  example (f : Y → Z) (g : X → Y) [IsSmoothT f] [IsSmoothT g] : IsSmoothT (f ∘ g) := by unfold Function.comp; infer_instance
  example (g : α → β) : IsSmoothT (λ (f : β → Z) (a : α) => (f (g a))) := by infer_instance
  example (f : Y → β → Z) (g : X → Y) (b : β) [IsSmoothT f] [IsSmoothT g] : IsSmoothT (λ x => f (g x) d) := by infer_instance
  example (f : Y → β → Z) (g : X → Y) (h : X → X) (b : β) [IsSmoothT f] [IsSmoothT g] [IsSmoothT h] : IsSmoothT (λ x => f (g (h (h x))) d) := by infer_instance
  example (f : α → Y → Z) [∀ a, IsSmoothT (f a)] : IsSmoothT (λ y a => f a y) := by infer_instance
  example (f : α → β → X → Y) [∀ a b, IsSmoothT (f a b)] : IsSmoothT (λ x b a => f a b x) := by infer_instance
  example (f : α → β → X → Y) [∀ a b, IsSmoothT (f a b)] : IsSmoothT (λ x a b => f a b x) := by infer_instance
  example (f : α → β → γ → X → Y) [∀ a b c, IsSmoothT (f a b c)] : IsSmoothT (λ x a b c => f a b c x) := by infer_instance
  example (f : X → X) [IsSmoothT f] : IsSmoothT (λ (g : X → X) x => f (f (g x))) := by infer_instance
  example (f : X → X → β → Y) [∀ x, IsSmoothT (f x)] [IsSmoothT λ x => λ y ⟿ f x y] : IsSmoothT (λ x b => f x x b) := by infer_instance
  example : IsSmoothT (λ (g : X → Y) (x : X) => F (g (h x)) a) := by infer_instance
  example : IsSmoothT (λ (x : X) => G' (h x) z w) := by infer_instance
  example (f : X → X → β → Y) [∀ x, IsSmoothT (f x)] [IsSmoothT λ x => λ y ⟿ f x y]  (b) : IsSmoothT (λ x => f x x b) := by infer_instance
  -- example (f : X → X → β → Y) (b) [IsSmoothNT 2 (λ x y => f x y b)] : IsSmoothT (λ x => f x x b) := by infer_instance
  example : IsSmoothT (λ (h : X → X) (x : X) => G (h x)) := by infer_instance

  example : IsSmoothT (λ (h : X → X) (x : X) => G (h x) a b) := by infer_instance
  example : IsSmoothT (λ (h : X → X) (x : X) => H a (h x) b) := by infer_instance
  example : IsSmoothT (λ (x : X) => h (F (h' ((h' ∘ g) (h x))) a)) := by unfold Function.comp; infer_instance
  example : IsSmoothT (λ (h'' : X → X) (x : X) => (h ∘ h ∘ h) (h (h'' (h ((h ∘ h) x))))) := by unfold Function.comp; infer_instance

end maintests

namespace foldtest

variable {α β γ : Type} 
variable {X : Type} {Y : Type} {Z : Type} [Vec X] [Vec Y] [Vec Z]

variable (f : X → X) [IsSmoothT f]

example : IsSmoothT (λ x => f x) := by infer_instance
example : IsSmoothT (λ x => f (f x)) := by infer_instance
example : IsSmoothT (λ (g : X → X) x => f (g x)) := by infer_instance
example : IsSmoothT (λ (g : X → X) x => g (f x)) := by infer_instance
example : IsSmoothT (λ (g : X ⟿ X) x => g (g x)) := by infer_instance
example : IsSmoothT (λ (g : X → X) x => f (f (g x))) := by infer_instance
example : IsSmoothT (λ (g : X → X) x => f (g (f x))) := by infer_instance
example : IsSmoothT (λ (g : X ⟿ X) x => f (g (g x))) := by infer_instance
example : IsSmoothT (λ (g : X → X)  x => g (f (f x))) := by infer_instance
example : IsSmoothT (λ (g : X ⟿ X) x => g (f (g x))) := by infer_instance
example : IsSmoothT (λ (g : X ⟿ X) x => g (g (f x))) := by infer_instance
example : IsSmoothT (λ (g : X ⟿ X) x => g (g (g x))) := by infer_instance
example : IsSmoothT (λ (g : X → X)  x => f (f (f (g x)))) := by infer_instance
example : IsSmoothT (λ (g : X → X)  x => f (f (g (f x)))) := by infer_instance
example : IsSmoothT (λ (g : X ⟿ X) x => f (f (g (g x)))) := by infer_instance
example : IsSmoothT (λ (g : X → X)  x => f (g (f (f x)))) := by infer_instance
example : IsSmoothT (λ (g : X ⟿ X) x => f (g (f (g x)))) := by infer_instance
example : IsSmoothT (λ (g : X ⟿ X) x => f (g (g (f x)))) := by infer_instance
example : IsSmoothT (λ (g : X ⟿ X) x => f (g (g (g x)))) := by infer_instance
example : IsSmoothT (λ (g : X → X)  x => g (f (f (f x)))) := by infer_instance

end foldtest


namespace forktest

variable {α β γ : Type} 
variable {X : Type} {Y : Type} {Z : Type} [Vec X] [Vec Y] [Vec Z]

variable (f : X → X → X) [∀ x, IsSmoothT (f x)] [IsSmoothT λ x => λ y ⟿ f x y]

example : IsSmoothT (λ x => f x x) := by infer_instance
example : IsSmoothT (λ x => f (f x x) x) := by infer_instance
example : IsSmoothT (λ x => f x (f x x)) := by infer_instance
example : IsSmoothT (λ x => f (f x x) (f x x)) := by infer_instance
example : IsSmoothT (λ x => f (f (f x x) x) x) := by infer_instance
example : IsSmoothT (λ x => f (f x (f x x)) x) := by infer_instance
example : IsSmoothT (λ x => f x (f (f x x) x)) := by infer_instance
example : IsSmoothT (λ x => f x (f x (f x x))) := by infer_instance

example : IsSmoothT (λ (g : X → X) x => f (g x) x) := by infer_instance
example : IsSmoothT (λ (g : X → X) x => f x (g x)) := by infer_instance
example : IsSmoothT (λ (g : X → X) x => f x (g x)) := by infer_instance

end forktest

namespace combtests
  variable {α β γ : Type} 
  variable {X : Type} {Y : Type} {Z : Type} [Vec X] [Vec Y] [Vec Z]

  example (f : X → X) [IsSmoothT f] : IsSmoothT ((f ∘ f) ∘ (f ∘ (f ∘ f))) := by unfold Function.comp; infer_instance
  example (f : β → X → Y) (g : α → β) (a : α) [IsSmoothT (f (g a))] : IsSmoothT ((f ∘ g) a) := by simp; infer_instance
  example (y : X) (A : X → X) (B : X → X) [IsSmoothT A] [IsSmoothT B] : IsSmoothT λ x => (B∘A) x + B (A (B x) + B x) := by unfold Function.comp; infer_instance
  example (y : X) (A : X → X) (B : X → X) [IsSmoothT A] [IsSmoothT B] : IsSmoothT (λ x : X => x + x) := by infer_instance
end combtests



section highorderfunctions

variable {X Y : Type} [Hilbert X] [Hilbert Y]

example : IsSmoothT fun (g : X⟿Y) => λ x ⟿ (c:ℝ) * g x := by infer_instance
example : IsSmoothT fun (g : ℝ⟿Y) => λ x ⟿ x * g x := by infer_instance
example : IsSmoothT fun (g : ℝ⟿ℝ) => λ x ⟿ g x * x := by apply IsSmoothT_rule_S₂ (λ (x y : ℝ) => y * x)
example  (f : X⟿Y) : IsSmoothT fun (g : X⟿Y) => λ x ⟿ ⟪f x, g x⟫ := by infer_instance
example  (f : X⟿Y) : IsSmoothT fun (g : X⟿Y) => λ x ⟿ ⟪g x, f x⟫ := by apply IsSmoothT_rule_S₂ (λ x y => ⟪y, f x⟫)
example  (f : X⟿Y) (A B : Y → Y) [IsSmoothT A] [IsSmooth B] : IsSmoothT fun (g : X⟿Y) => λ x ⟿ ⟪A (g x), B (f x)⟫ := by apply IsSmoothT_rule_S₂ (λ x y => ⟪A y, B (f x)⟫)
example : IsSmoothT fun (g : ℝ⟿Y) => λ x ⟿ x * g x := by infer_instance

end highorderfunctions


section argument_shuffling




-- Test in forgeting smoothenss in various components

--IsSmoothN 2 to IsSmooth
example (f : X → Y → Z) [IsSmoothN 2 f]
  : IsSmoothT f := by infer_instance

example (f : X → Y → Z) [IsSmoothN 2 f] (x : X)
  : IsSmoothT (f x) := by infer_instance

example (f : X → Y → Z) [IsSmoothN 2 f] (y : Y)
  : IsSmoothT (λ y => f x y) := by infer_instance


-- IsSmoothN 3 to IsSmooth
example (f : X → Y → Z → W) [IsSmoothN 3 f]
  : IsSmoothT (λ x y z => f x y z) := by infer_instance

example (f : X → Y → Z → W) [IsSmoothN 3 f] (x : X)
  : IsSmoothT (f x) := by infer_instance

example (f : X → Y → Z → W) [IsSmoothN 3 f] (x : X) (y : Y)
  : IsSmoothT (f x y) := by infer_instance

example (f : X → Y → Z → W) [IsSmoothN 3 f] (x : X) (z : Z)
  : IsSmoothT (λ y => f x y z) := by infer_instance

example (f : X → Y → Z → W) [IsSmoothN 3 f] (y : Y) (z : Z)
  : IsSmoothT (λ x => f x y z) := by infer_instance


-- IsSmoothN 3 to effectively IsSmoothN 2
example (f : X → Y → Z → W) [IsSmoothN 3 f]
  : IsSmoothT (λ x => λ y ⟿ λ z => f x y z) := by infer_instance

example (f : X → Y → Z → W) [IsSmoothN 3 f]
  : IsSmoothT (λ x => λ z ⟿ λ y => f x y z) := by infer_instance

example (f : X → Y → Z → W) [IsSmoothN 3 f]
  : IsSmoothT (λ y => λ x ⟿ λ z => f x y z) := by infer_instance
set_option synthInstance.maxSize 300 in
example (f : X → Y → Z → W) [IsSmoothN 3 f]
  : IsSmoothT (λ y => λ z ⟿ λ x => f x y z) := by infer_instance
set_option synthInstance.maxSize 300 in
example (f : X → Y → Z → W) [IsSmoothN 3 f]
  : IsSmoothT (λ z => λ x ⟿ λ y => f x y z) := by infer_instance
set_option synthInstance.maxSize 500 in
example (f : X → Y → Z → W) [IsSmoothN 3 f]
  : IsSmoothT (λ z => λ y ⟿ λ x => f x y z) := by infer_instance

example (f : X → Y → Z → W) [IsSmoothN 3 f] (z : Z)
  : IsSmoothT (λ x => λ y ⟿ f x y z) := by infer_instance

example (f : X → Y → Z → W) [IsSmoothN 3 f] (y : Y)
  : IsSmoothT (λ x => λ z ⟿ f x y z) := by infer_instance

example (f : X → Y → Z → W) [IsSmoothN 3 f] (x : X)
  : IsSmoothT (λ y => λ z ⟿ f x y z) := by infer_instance


-- Duplicating arguments
example (f : X → X → Z) [IsSmoothN 2 f]
  : IsSmoothT (λ x => f x x) := by infer_instance

example (f : X → X → X → Z) [IsSmoothN 3 f]
  : IsSmoothT (λ x => λ y ⟿ f x x y) := by infer_instance

example (f : X → X → X → Z) [IsSmoothN 3 f]
  : IsSmoothT (λ x => λ y ⟿ f x x y) := by infer_instance

example (f : X → X → X → Z) [IsSmoothN 3 f]
  : IsSmoothT (λ x => λ y ⟿ f x y x) := by infer_instance

example (f : X → X → X → Z) [IsSmoothN 3 f]
  : IsSmoothT (λ x => λ y ⟿ f y x x) := by infer_instance

example (f : X → X → X → Z) [IsSmoothN 3 f]
  : IsSmoothT (λ x => λ y ⟿ f x y y) := by infer_instance

example (f : X → X → X → Z) [IsSmoothN 3 f]
  : IsSmoothT (λ x => λ y ⟿ f y x y) := by infer_instance

example (f : X → X → X → Z) [IsSmoothN 3 f]
  : IsSmoothT (λ x => λ y ⟿ f x y y) := by infer_instance

-- Permuting arguments
example (f : X → Y → Z → W) [IsSmoothN 3 f]
  : IsSmoothT (λ x => λ z y ⟿ f x y z) := by infer_instance

example (f : X → Y → Z → W) [IsSmoothN 3 f]
  : IsSmoothT (λ x => λ z ⟿ f x y z) := by infer_instance

example (f : X → Y → Z → W) [IsSmoothN 3 f]
  : IsSmoothT (λ x y => λ z ⟿ f x y z) := by infer_instance

example (f : X → Y → Z → W) [IsSmoothN 3 f]
  : IsSmoothT (λ y => λ x z ⟿ f x y z) := by infer_instance

example (f : X → Y → Z → W) [IsSmoothN 3 f]
  : IsSmoothT (λ z => λ x y ⟿ f x y z) := by infer_instance

example (f : X → Y → Z → W) [IsSmoothN 3 f]
  : IsSmoothT (λ y => λ x z ⟿ f x y z) := by infer_instance


end argument_shuffling
