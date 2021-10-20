import SciLean.Categories.Smooth

set_option synthInstance.maxHeartbeats 5000
set_option synthInstance.maxSize 1000

namespace SciLean.Smooth.Tests

variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

namespace maintests

  variable {α β γ : Type}

  variable (f : Y → Z) (g : X → Y) [IsSmooth f] [IsSmooth g] (h : X → X) [IsSmooth h] (h' : Y → Y) [IsSmooth h']
  variable (a : α) (b : β)
  variable (F : Y → α → X) [IsSmooth (λ y => F y a)]
  variable (G : X → α → β → Y) [IsSmooth (λ x => G x a b)]
  variable (G' : X → Z → W → Y) (z : Z) (w : W) [IsSmooth (λ x => G' x z w)]
  variable (H : α → X → β → Y) [IsSmooth (λ x => H a x b)]
  variable (H': α → β → X → Y) [IsSmooth (λ x => H' a b x)]

  def test1 : IsSmooth (λ x => g x) := by infer_instance
  def test2 : IsSmooth (λ x => f (g x)) := by infer_instance
  def test3 : IsSmooth (λ x => f (g (h (h x)))) := by infer_instance
  def test4 : IsSmooth (λ (g' : X → Y) => f ∘ g') := by infer_instance
  def test5 : IsSmooth (λ (x : X) => F (g (h x)) a) := by infer_instance
  def test6 : IsSmooth (λ (x : X) => h (F (h' ((h' ∘ g) (h x))) a)) := by simp; infer_instance
  def test7 : IsSmooth (f ∘ g) := by simp; infer_instance
  def test8 : IsSmooth (λ (f : Y → Z) (x : X) => (f (g x))) := by infer_instance
  def test9 : IsSmooth (λ (h'' : X → X) (x : X) => (h (h'' ((h ∘ h) x)))) := by infer_instance
  def test10 : IsSmooth (λ (h'' : X → X) (x : X) => (h ∘ h ∘ h) (h (h'' (h ((h ∘ h) x))))) := by infer_instance
  def test11 : IsSmooth (λ (x : X) => G (h x) a b) := by infer_instance
  def test12 : IsSmooth (λ (x : X) => H a (h x) b) := by infer_instance
  def test13 : IsSmooth (λ (x : X) => H' a b (h x)) := by infer_instance
  def test14 (f : β → Y → Z) [∀ b, IsSmooth (f b)] : IsSmooth (λ (g : α → Y) (b : β) (a : α) => f b (g a)) := by infer_instance
  def test15 (f : X → X → Y) [IsSmooth f] [∀ x, IsSmooth (f x)] : IsSmooth (λ x => f x x) := by infer_instance
  def test16 (f : X → X → Y) [IsSmooth f] [∀ x, IsSmooth (f x)] : IsSmooth (λ x => f (h x) x) := by infer_instance
  def test17 (f : X → α → X → Y) (a : α) [IsSmooth (λ x y => f x a y)] [∀ x, IsSmooth (λ y => f x a y)] : IsSmooth (λ x => f x a x) := by infer_instance
  def test18 (f : X → α → X → Y) (a : α) [IsSmooth (λ x y => f x a y)] [∀ x, IsSmooth (λ y => f x a y)] : IsSmooth (λ x => f (h x) a x) := by infer_instance
  def test19 (f : X → X → Y) [IsSmooth f] [∀ x, IsSmooth (f x)] : IsSmooth (λ x => f x (h x)) := by infer_instance
  def test20 : IsSmooth (λ (g : X → Y) (x : X) => F (g (h x)) a) := by infer_instance
  def test21 (f : X → α → X → Y) (a : α) [IsSmooth (λ x y => f x a y)] [∀ x, IsSmooth (λ y => f x a y)] : IsSmooth (λ x => f x a (h x)) := by infer_instance
  def test22 (f : X → α → X → Y) (a : α) [IsSmooth (λ x y => f x a y)] [∀ x, IsSmooth (λ y => f x a y)] : IsSmooth (λ x => f (h x) a (h x)) := by infer_instance
  def test23 (f : X → α → X → Y) (a : α) [IsSmooth (λ x y => f x a y)] [∀ x, IsSmooth (λ y => f x a y)] : IsSmooth (λ (h : X → X) x => f (h x) a (h x)) := by infer_instance
  def test24 : IsSmooth (λ (h : X → X) (x : X) => G (h x) a b) := by infer_instance
  def test25 : IsSmooth (λ (h : X → X) (x : X) => H a (h x) b) := by infer_instance
  def test26 : IsSmooth (λ (h : X → X) (x : X) => H' a b (h x)) := by infer_instance
  def test27 (f : X → X → α → Y) (a : α) [IsSmooth (λ x y => f x y a)] [∀ x, IsSmooth (λ y => f x y a)] : IsSmooth (λ x => f (h x) x a) := by infer_instance
  def test28 : IsSmooth (λ (x : X) => G' (h x) z w) := by infer_instance

end maintests

namespace combtests
variable {α β γ : Type} 
variable {X : Type} {Y : Type} {Z : Type} [Vec X] [Vec Y] [Vec Z]

theorem test1 (f : X → X) [IsSmooth f] : IsSmooth ((f ∘ f) ∘ (f ∘ (f ∘ f))) := by infer_instance
theorem test2 (f : β → X → Y) (g : α → β) (a : α) [IsSmooth (f (g a))] : IsSmooth ((f ∘ g) a) := by infer_instance
-- theorem test3 (y : X) (A : X → X) (B : X → X) [IsSmooth A] [IsSmooth B] : IsSmooth λ x => (B∘A) x + B (A (B x) + B x) := by infer_instance
 
end combtests
