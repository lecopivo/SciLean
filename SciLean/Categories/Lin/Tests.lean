import SciLean.Categories.Lin

namespace SciLean.Lin.Tests

set_option synthInstance.maxHeartbeats 5000

variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

namespace maintests

  variable {α β γ : Type}

  variable (f : Y → Z) (g : X → Y) [IsLin f] [IsLin g] (h : X → X) [IsLin h] (h' : Y → Y) [IsLin h']
  variable (F : Y → α → X) [IsLin F]
  variable (G : X → α → β → Y) [IsLin G]
  variable (H : α → X → β → Y) [∀ a, IsLin (H a)]
  variable (H': α → β → X → Y) [∀ a b, IsLin (H' a b)]

  def test1 : IsLin (λ x => g x) := by infer_instance
  def test2 : IsLin (λ x => f (g x)) := by infer_instance
  def test3 : IsLin (λ x => f (g (h (h x)))) := by infer_instance
  def test4 : IsLin (λ (g' : X → Y) => f ∘ g') := by infer_instance
  def test5 : IsLin (λ (x : X) => F (g (h x)) a) := by infer_instance
  def test6 : IsLin (λ (x : X) => h (F (h' ((h' ∘ g) (h x))) a)) := by simp; infer_instance
  def test7 : IsLin (f ∘ g) := by simp; infer_instance
  def test8 : IsLin (λ (f : Y → Z) (x : X) => (f (g x))) := by infer_instance
  def test9 : IsLin (λ (h'' : X → X) (x : X) => (h (h'' ((h ∘ h) x)))) := by infer_instance
  def test10 : IsLin (λ (h'' : X → X) (x : X) => (h ∘ h ∘ h) (h (h'' (h ((h ∘ h) x))))) := by infer_instance
  def test11 : IsLin (λ (x : X) => G (h x) a b) := by infer_instance
  def test12 : IsLin (λ (x : X) => H a (h x) b) := by infer_instance
  def test13 : IsLin (λ (x : X) => H' a b (h x)) := by infer_instance
  def test14 (f : β → Y → Z) [∀ b, IsLin (f b)] : IsLin (λ (g : α → Y) (b : β) (a : α) => f b (g a)) := by infer_instance
  def test15 (f : X → X → Y) [IsLin (λ xx : X×X => f xx.1 xx.2)] : IsLin (λ x => f x x) := by infer_instance
  def test16 (f : X → X → Y) [IsLin (λ xx : X×X => f xx.1 xx.2)] : IsLin (λ x => f (h x) x) := by infer_instance
  -- def test17 (f : X → α → X → Y) (a : α) [IsLin (λ xx : X×X => f xx.1 a xx.2)] : IsLin (λ x => f x a x) := by infer_instance
  -- def test18 (f : X → α → X → Y) (a : α) [IsLin (λ xx : X×X => f xx.1 a xx.2)] : IsLin (λ x => f (h x) a x) := by infer_instance
  def test19 (f : X → X → Y) [IsLin (λ xx : X×X => f xx.1 xx.2)] : IsLin (λ x => f x (h x)) := by infer_instance
  def test20 : IsLin (λ (g : X → Y) (x : X) => F (g (h x)) a) := by infer_instance
  -- def test21 (f : X → α → X → Y) (a : α) [IsLin (λ xx : X×X => f xx.1 a xx.2)] : IsLin (λ x => f x a (h x)) := by infer_instance
  -- def test22 (f : X → α → X → Y) (a : α) [IsLin (λ xx : X×X => f xx.1 a xx.2)] : IsLin (λ x => f (h x) a (h x)) := by infer_instance
  -- def test23 (f : X → α → X → Y) (a : α) [IsLin (λ xx : X×X => f xx.1 a xx.2)] : IsLin (λ (h : X → X) x => f (h x) a (h x)) := by infer_instance
  def test24 : IsLin (λ (h : X → X) (x : X) => G (h x) a b) := by infer_instance
  def test25 : IsLin (λ (h : X → X) (x : X) => H a (h x) b) := by infer_instance
  def test26 : IsLin (λ (h : X → X) (x : X) => H' a b (h x)) := by infer_instance
  -- def test27 (f : X → X → α → Y) (a : α) [IsLin (λ xx : X×X => f xx.1 xx.2 a)] : IsLin (λ x => f (h x) x a) := by infer_instance

  -- set_option trace.Meta.synthInstance true
  -- def test29 (f : X → Y → Z) (y : Y) [IsLin (λ xy : X×Y => f xy.1 xy.2)] : IsLin (λ x => f x y) := by infer_instance
  -- set_option trace.Meta.synthInstance false

end maintests

namespace combtests
variable {α β γ : Type} 
variable {X : Type} {Y : Type} {Z : Type} [Vec X] [Vec Y] [Vec Z]

theorem test1 (f : X → X) [IsLin f] : IsLin ((f ∘ f) ∘ (f ∘ (f ∘ f))) := by infer_instance
-- theorem test2 (f : β → X → Y) (g : α → β) (a : α) [IsLin (f (g a))] : IsLin ((f ∘ g) a) := by infer_instance
theorem test3 (y : X) (A : X → X) (B : X → X) [IsLin A] [IsLin B] : IsLin λ x => (B∘A) x + B (A (B x) + B x) := by infer_instance
 
end combtests

namespace hilbert

variable {U V W : Type} [Hilbert U] [Hilbert V] [Hilbert W]

-- example (d) : IsLin λ (u v : U) => (u, v)_[d] := by infer_instance
-- example : IsLin λ u : U => ⟨u,u'⟩ := by infer_instance


-- example (v : ℝ×ℝ) : IsLin (λ u : ℝ×ℝ => ⟨u, v⟩) := by infer_instance

-- set_option trace.Meta.synthInstance.tryResolve false
-- set_option trace.Meta.synthInstance.generate false
-- example : SemiInner ℝ := by infer_instance
-- example : Hilbert ℝ := by infer_instance
-- example : IsLin (SemiInner.semi_inner : U → U → _ → ℝ) := by infer_instance
-- example : IsLin (SemiInner.semi_inner : ℝ → ℝ → _ → ℝ) := by infer_instance
-- example : IsLin (SemiInner.semi_inner : ℝ×ℝ → ℝ×ℝ → _ → ℝ) := by infer_instance

end hilbert 
