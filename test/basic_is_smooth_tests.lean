import SciLean.Basic


namespace SciLean.Smooth.Tests

variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

namespace maintests

  variable {α β γ : Type}

  variable (f : Y → Z) (g : X → Y) [IsSmooth f] [IsSmooth g] (h : X → X) [IsSmooth h] (h' : Y → Y) [IsSmooth h']
  variable (a : α) (b : β)
  variable (F : Y → α → X) [IsSmooth F]
  variable (G : X → α → β → Y) [IsSmooth G]
  variable (G' : X → Z → W → Y) (z : Z) (w : W) [IsSmooth G']
  variable (H : α → X → β → Y) [IsSmooth (H a)]
  variable (H': α → β → X → Y) [IsSmooth (H' a b)]

  example : IsSmooth (λ x => g x) := by infer_instance
  example : IsSmooth (λ x => f (g x)) := by infer_instance
  example : IsSmooth (λ x => f (g (h (h x)))) := by infer_instance
  example : IsSmooth (λ (g' : X → Y) => f ∘ g') := by infer_instance
  example : IsSmooth (λ (x : X) => F (g (h x)) a) := by infer_instance
  example : IsSmooth (f ∘ g) := by infer_instance
  example : IsSmooth (λ (f : Y → Z) (x : X) => (f (g x))) := by infer_instance
  example : IsSmooth (λ (h'' : X → X) (x : X) => h (h (h (h'' ((h ∘ h) (h x)))))) := by infer_instance
  example : IsSmooth (λ (x : X) => G (h x) a b) := by infer_instance
  example : IsSmooth (λ (x : X) => H a (h x) b) := by infer_instance
  example : IsSmooth (λ (x : X) => H' a b (h x)) := by infer_instance
  example (f : β → Y → Z) [∀ b, IsSmooth (f b)] : IsSmooth (λ (g : α → Y) (b : β) (a : α) => f b (g a)) := by infer_instance
  example (f : X → X → Y) [IsSmooth f] [∀ x, IsSmooth (f x)] : IsSmooth (λ x => f x x) := by infer_instance
  example (f : X → X → Y) [IsSmooth f] [∀ x, IsSmooth (f x)] : IsSmooth (λ x => f (h x) x) := by infer_instance
  example (f : X → X → Y) [IsSmooth f] [∀ x, IsSmooth (f x)] : IsSmooth (λ x => f x (h x)) := by infer_instance
  example : IsSmooth (λ (h : X → X) (x : X) => H' a b (h x)) := by infer_instance
  example (f : Y → Z) (g : X → Y) [IsSmooth f] [IsSmooth g] : IsSmooth (f ∘ g) := by infer_instance
  example (g : α → β) : IsSmooth (λ (f : β → Z) (a : α) => (f (g a))) := by infer_instance
  example (f : Y → β → Z) (g : X → Y) (b : β) [IsSmooth f] [IsSmooth g] : IsSmooth (λ x => f (g x) d) := by infer_instance
  example (f : Y → β → Z) (g : X → Y) (h : X → X) (b : β) [IsSmooth f] [IsSmooth g] [IsSmooth h] : IsSmooth (λ x => f (g (h (h x))) d) := by infer_instance
  example (f : α → Y → Z) [∀ a, IsSmooth (f a)] : IsSmooth (λ y a => f a y) := by infer_instance
  example (f : α → β → X → Y) [∀ a b, IsSmooth (f a b)] : IsSmooth (λ x b a => f a b x) := by infer_instance
  example (f : α → β → X → Y) [∀ a b, IsSmooth (f a b)] : IsSmooth (λ x a b => f a b x) := by infer_instance
  example (f : α → β → γ → X → Y) [∀ a b c, IsSmooth (f a b c)] : IsSmooth (λ x a b c => f a b c x) := by infer_instance
  example (f : X → X) [IsSmooth f] : IsSmooth (λ (g : X → X) x => f (f (g x))) := by infer_instance
  example (f : X → X → β → Y) [IsSmooth f] [∀ x, IsSmooth (f x)] : IsSmooth (λ x b => f x x b) := by infer_instance
  example (f : X → X → β → Y) [IsLin f] [∀ x, IsLin (f x)] : IsSmooth (λ x b => f x x b) := by infer_instance
  example : IsSmooth (λ (g : X → Y) (x : X) => F (g (h x)) a) := by infer_instance
  example : IsSmooth (λ (x : X) => G' (h x) z w) := by infer_instance
  example (f : X → X → β → Y) [IsSmooth f] [∀ x, IsSmooth (f x)] (b) : IsSmooth (λ x => f x x b) := by infer_instance
  example (f : X → X → β → Y) [IsLin f] [∀ x, IsLin (f x)] (b) : IsSmooth (λ x => f x x b) := by infer_instance
  example : IsSmooth (λ (h : X → X) (x : X) => G (h x)) := by infer_instance

  set_option synthInstance.maxHeartbeats 5000
  set_option trace.Meta.synthInstance true in
  example : IsSmooth (λ (h : X → X) (x : X) => G (h x) a b) := by infer_instance
  example : IsSmooth (λ (h : X → X) (x : X) => H a (h x) b) := by infer_instance
  example : IsSmooth (λ (x : X) => h (F (h' ((h' ∘ g) (h x))) a)) := by infer_instance
  example : IsSmooth (λ (h'' : X → X) (x : X) => (h ∘ h ∘ h) (h (h'' (h ((h ∘ h) x))))) := by infer_instance
  set_option synthInstance.maxHeartbeats 500

end maintests

namespace foldtest

variable {α β γ : Type} 
variable {X : Type} {Y : Type} {Z : Type} [Vec X] [Vec Y] [Vec Z]

variable (f : X → X) [IsSmooth f]

set_option synthInstance.maxHeartbeats 5000

example : IsSmooth (λ x => f x) := by infer_instance
example : IsSmooth (λ x => x |> f) := by infer_instance
example : IsSmooth (λ x => x |> f |> f) := by infer_instance
example : IsSmooth (λ (g : X → X) x => f (g x)) := by infer_instance
example : IsSmooth (λ (g : X → X) x => g (f x)) := by infer_instance
example : IsSmooth (λ (g : X ⟿ X) x => x |> g |> g) := by infer_instance
example : IsSmooth (λ (g : X → X) x => f (f (g x))) := by infer_instance
example : IsSmooth (λ (g : X → X) x => f (g (f x))) := by infer_instance
example : IsSmooth (λ (g : X ⟿ X) x => x |> g |> g |> f) := by infer_instance
example : IsSmooth (λ (g : X → X) x => g (f (f x))) := by infer_instance
example : IsSmooth (λ (g : X ⟿ X) x => x |> g |> f |> g) := by infer_instance
example : IsSmooth (λ (g : X ⟿ X) x => x |> f |> g |> g) := by infer_instance
-- example : IsSmooth (λ (g : X ⟿ X) x => x |> g |> g |> g) := by infer_instance
example : IsSmooth (λ (g : X → X) x => x |> g |> f |> f |> f) := by infer_instance
example : IsSmooth (λ (g : X → X) x => x |> f |> g |> f |> f) := by infer_instance
example : IsSmooth (λ (g : X ⟿ X) x => x |> g |> g |> f |> f) := by infer_instance
example : IsSmooth (λ (g : X → X) x => x |> f |> f |> g |> f) := by infer_instance
example : IsSmooth (λ (g : X ⟿ X) x => x |> g |> f |> g |> f) := by infer_instance
example : IsSmooth (λ (g : X ⟿ X) x => x |> f |> g |> g |> f) := by infer_instance
-- example : IsSmooth (λ (g : X ⟿ X) x => x |> g |> g |> g |> f) := by infer_instance
example : IsSmooth (λ (g : X → X) x => x |> f |> f |> f |> g) := by infer_instance

end foldtest


namespace forktest

variable {α β γ : Type} 
variable {X : Type} {Y : Type} {Z : Type} [Vec X] [Vec Y] [Vec Z]

variable (f : X → X → X) [IsSmooth f] [∀ x, IsSmooth (f x)]

example : IsSmooth (λ x => f x x) := by infer_instance
example : IsSmooth (λ x => f (f x x) x) := by infer_instance
example : IsSmooth (λ x => f x (f x x)) := by infer_instance
example : IsSmooth (λ x => f (f x x) (f x x)) := by infer_instance
example : IsSmooth (λ x => f (f (f x x) x) x) := by infer_instance
example : IsSmooth (λ x => f (f x (f x x)) x) := by infer_instance
example : IsSmooth (λ x => f x (f (f x x) x)) := by infer_instance
example : IsSmooth (λ x => f x (f x (f x x))) := by infer_instance

example : IsSmooth (λ (g : X → X) x => f (g x) x) := by infer_instance
example : IsSmooth (λ (g : X → X) x => f x (g x)) := by infer_instance
example : IsSmooth (λ (g : X → X) x => f x (g x)) := by infer_instance

end forktest

namespace combtests
  variable {α β γ : Type} 
  variable {X : Type} {Y : Type} {Z : Type} [Vec X] [Vec Y] [Vec Z]

  example (f : X → X) [IsSmooth f] : IsSmooth ((f ∘ f) ∘ (f ∘ (f ∘ f))) := by infer_instance
  example (f : β → X → Y) (g : α → β) (a : α) [IsSmooth (f (g a))] : IsSmooth ((f ∘ g) a) := by simp infer_instance
  example (y : X) (A : X → X) (B : X → X) [IsSmooth A] [IsSmooth B] : IsSmooth λ x => (B∘A) x + B (A (B x) + B x) := by infer_instance
  example (y : X) (A : X → X) (B : X → X) [IsSmooth A] [IsSmooth B] : IsSmooth (λ x : X => x + x) := by infer_instance
end combtests

