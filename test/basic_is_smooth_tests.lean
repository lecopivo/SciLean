-- import SciLean.Core.IsSmooth
import SciLean.Core.CoreFunctionProperties

namespace SciLean.Smooth.Tests

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
  example : IsSmoothT (λ (g' : X → Y) => f ∘ g') := by infer_instance
  example : IsSmoothT (λ (x : X) => F (g (h x)) a) := by infer_instance
  example : IsSmoothT (f ∘ g) := by infer_instance
  example : IsSmoothT (λ (f : Y → Z) (x : X) => (f (g x))) := by infer_instance
  example : IsSmoothT (λ (h'' : X → X) (x : X) => h (h (h (h'' ((h ∘ h) (h x)))))) := by infer_instance
  example : IsSmoothT (λ (x : X) => G (h x) a b) := by infer_instance
  example : IsSmoothT (λ (x : X) => H a (h x) b) := by infer_instance
  example : IsSmoothT (λ (x : X) => H' a b (h x)) := by infer_instance
  example (f : β → Y → Z) [∀ b, IsSmoothT (f b)] : IsSmoothT (λ (g : α → Y) (b : β) (a : α) => f b (g a)) := by infer_instance
  example (f : X → X → Y) [IsSmoothNT 2 f]: IsSmoothT (λ x => f x x) := by infer_instance
  example (f : X → X → Y) [IsSmoothNT 2 f]: IsSmoothT (λ x => f (h x) x) := by infer_instance
  example (f : X → X → Y) [IsSmoothNT 2 f] : IsSmoothT (λ x => f x (h x)) := by infer_instance
  example : IsSmoothT (λ (h : X → X) (x : X) => H' a b (h x)) := by infer_instance
  example (f : Y → Z) (g : X → Y) [IsSmoothT f] [IsSmoothT g] : IsSmoothT (f ∘ g) := by infer_instance
  example (g : α → β) : IsSmoothT (λ (f : β → Z) (a : α) => (f (g a))) := by infer_instance
  example (f : Y → β → Z) (g : X → Y) (b : β) [IsSmoothT f] [IsSmoothT g] : IsSmoothT (λ x => f (g x) d) := by infer_instance
  example (f : Y → β → Z) (g : X → Y) (h : X → X) (b : β) [IsSmoothT f] [IsSmoothT g] [IsSmoothT h] : IsSmoothT (λ x => f (g (h (h x))) d) := by infer_instance
  example (f : α → Y → Z) [∀ a, IsSmoothT (f a)] : IsSmoothT (λ y a => f a y) := by infer_instance
  example (f : α → β → X → Y) [∀ a b, IsSmoothT (f a b)] : IsSmoothT (λ x b a => f a b x) := by infer_instance
  example (f : α → β → X → Y) [∀ a b, IsSmoothT (f a b)] : IsSmoothT (λ x a b => f a b x) := by infer_instance
  example (f : α → β → γ → X → Y) [∀ a b c, IsSmoothT (f a b c)] : IsSmoothT (λ x a b c => f a b c x) := by infer_instance
  example (f : X → X) [IsSmoothT f] : IsSmoothT (λ (g : X → X) x => f (f (g x))) := by infer_instance
  example (f : X → X → β → Y) [IsSmoothNT 2 f] : IsSmoothT (λ x b => f x x b) := by infer_instance
  example : IsSmoothT (λ (g : X → Y) (x : X) => F (g (h x)) a) := by infer_instance
  example : IsSmoothT (λ (x : X) => G' (h x) z w) := by infer_instance
  example (f : X → X → β → Y) [IsSmoothNT 2 f]  (b) : IsSmoothT (λ x => f x x b) := by infer_instance
  -- example (f : X → X → β → Y) (b) [IsSmoothNT 2 (λ x y => f x y b)] : IsSmoothT (λ x => f x x b) := by infer_instance
  example : IsSmoothT (λ (h : X → X) (x : X) => G (h x)) := by infer_instance

  example : IsSmoothT (λ (h : X → X) (x : X) => G (h x) a b) := by infer_instance
  example : IsSmoothT (λ (h : X → X) (x : X) => H a (h x) b) := by infer_instance
  example : IsSmoothT (λ (x : X) => h (F (h' ((h' ∘ g) (h x))) a)) := by infer_instance
  example : IsSmoothT (λ (h'' : X → X) (x : X) => (h ∘ h ∘ h) (h (h'' (h ((h ∘ h) x))))) := by infer_instance

end maintests

namespace foldtest

variable {α β γ : Type} 
variable {X : Type} {Y : Type} {Z : Type} [Vec X] [Vec Y] [Vec Z]

variable (f : X → X) [IsSmoothT f]


example : IsSmoothT (λ x => f x) := by infer_instance
example : IsSmoothT (λ x => x |> f) := by infer_instance
example : IsSmoothT (λ x => x |> f |> f) := by infer_instance
example : IsSmoothT (λ (g : X → X) x => f (g x)) := by infer_instance
example : IsSmoothT (λ (g : X → X) x => g (f x)) := by infer_instance
-- example : IsSmoothT (λ (g : X ⟿ X) x => x |> g |> g) := by infer_instance
example : IsSmoothT (λ (g : X → X) x => f (f (g x))) := by infer_instance
example : IsSmoothT (λ (g : X → X) x => f (g (f x))) := by infer_instance
-- example : IsSmoothT (λ (g : X ⟿ X) x => x |> g |> g |> f) := by infer_instance
example : IsSmoothT (λ (g : X → X) x => g (f (f x))) := by infer_instance
-- example : IsSmoothT (λ (g : X ⟿ X) x => x |> g |> f |> g) := by infer_instance
-- set_option synthInstance.maxHeartbeats 10000 in
-- example : IsSmoothT (λ (g : X ⟿ X) x => x |> f |> g |> g) := by infer_instance
-- example : IsSmoothT (λ (g : X ⟿ X) x => x |> g |> g |> g) := by infer_instance
example : IsSmoothT (λ (g : X → X) x => x |> g |> f |> f |> f) := by infer_instance
example : IsSmoothT (λ (g : X → X) x => x |> f |> g |> f |> f) := by infer_instance
-- example : IsSmoothT (λ (g : X ⟿ X) x => x |> g |> g |> f |> f) := by infer_instance
example : IsSmoothT (λ (g : X → X) x => x |> f |> f |> g |> f) := by infer_instance
-- example : IsSmoothT (λ (g : X ⟿ X) x => x |> g |> f |> g |> f) := by infer_instance
-- set_option synthInstance.maxHeartbeats 10000 in
-- example : IsSmoothT (λ (g : X ⟿ X) x => x |> f |> g |> g |> f) := by infer_instance
-- example : IsSmoothT (λ (g : X ⟿ X) x => x |> g |> g |> g |> f) := by infer_instance
example : IsSmoothT (λ (g : X → X) x => x |> f |> f |> f |> g) := by infer_instance

end foldtest


namespace forktest

variable {α β γ : Type} 
variable {X : Type} {Y : Type} {Z : Type} [Vec X] [Vec Y] [Vec Z]

variable (f : X → X → X) [IsSmoothNT 2 f]

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

  example (f : X → X) [IsSmoothT f] : IsSmoothT ((f ∘ f) ∘ (f ∘ (f ∘ f))) := by infer_instance
  example (f : β → X → Y) (g : α → β) (a : α) [IsSmoothT (f (g a))] : IsSmoothT ((f ∘ g) a) := by simp; infer_instance
  example (y : X) (A : X → X) (B : X → X) [IsSmoothT A] [IsSmoothT B] : IsSmoothT λ x => (B∘A) x + B (A (B x) + B x) := by infer_instance
  example (y : X) (A : X → X) (B : X → X) [IsSmoothT A] [IsSmoothT B] : IsSmoothT (λ x : X => x + x) := by infer_instance
end combtests

