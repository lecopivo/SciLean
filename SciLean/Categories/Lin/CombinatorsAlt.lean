import SciLean.Categories.Lin.Basic

set_option synthInstance.maxHeartbeats 5000
set_option synthInstance.maxSize 1000

namespace SciLean.Lin

variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

-- id
instance : IsLin (id : X → X) := sorry
instance : IsLin (λ x : X => x) := sorry

-- constant
instance : IsLin (λ (x : X) (b : β) => x) := sorry
instance : IsLin (λ (y : Y) => (0 : X)) := sorry

-- swaping arguments
instance : IsLin (λ (f : α → β → Z) (b : β) (a : α) => f a b) := sorry
instance (f : α → Y → Z) [∀ a, IsLin (f a)] : IsLin (λ (y : Y) (a : α) => f a y) := sorry
instance (f : X → β → Z) (b : β) [IsLin f] : IsLin (λ (x : X) => f x b) := sorry

----------------
-- evaluation --
----------------
instance : IsLin (λ (f : α → Y) (a : α) => f a) := sorry
-- instance (f : Y → Z) [IsLin f] : IsLin (λ (g : α → Y) (a : α) => f (g a)) := sorry

-----------------
-- compitision --
-----------------
instance (f : Y → Z) [IsLin f] (g : X → Y) [IsLin g] 
         : IsLin (λ x => f (g x)) := sorry

-- one extra arg
instance (f : Y → α → Z) (g : X → Y) (a : α) [IsLin g] [IsLin (λ y => f y a)] 
         : IsLin (λ x => f (g x) a) := sorry

-- two extra arg
instance (f : Y → α → β → Z) (g : X → Y) (a : α) (b : β) [IsLin g] [IsLin (λ y => f y a b)] 
         : IsLin (λ x => f (g x) a b) := sorry

-- three extra arg
instance (f : Y → α → β → γ → Z) (g : X → Y) (a : α) (b : β) (c : γ) [IsLin g] [IsLin (λ y => f y a b c)] 
         : IsLin (λ x => f (g x) a b c) := sorry
-- ... This continues to infinity :( ... How to deal with these???

--------------
-- diagonal --
--------------
instance (f : X → Y → Z) [IsLin (λ p : X×Y => f p.1 p.2)] (g : W → X) [IsLin g] (h : W → Y) [IsLin h]
         : IsLin (λ w => f (g w) (h w)) := sorry

-- one extra arg
instance (f : X → α → Y → Z) (a : α) [IsLin (λ p : X × Y => f p.1 a p.2)] (g : W → X) [IsLin g] (h : W → Y) [IsLin h]
         : IsLin (λ w => f (g w) a (h w)) := sorry
instance (f : X → Y → α → Z) (a : α) [IsLin (λ p : X × Y => f p.1 p.2 a)] (g : W → X) [IsLin g] (h : W → Y) [IsLin h]
         : IsLin (λ w => f (g w) (h w) a) := sorry

-- two extra arg
instance (f : X → α → β → Y → Z) (a : α) (b : β) [IsLin (λ p : X × Y => f p.1 a b p.2)] (g : W → X) [IsLin g] (h : W → Y) [IsLin h]
         : IsLin (λ w => f (g w) a b (h w)) := sorry
instance (f : X → α → Y → β → Z) (a : α) (b : β) [IsLin (λ p : X × Y => f p.1 a p.2 b)] (g : W → X) [IsLin g] (h : W → Y) [IsLin h]
         : IsLin (λ w => f (g w) a (h w) b) := sorry
instance (f : X → Y → α → β → Z) (a : α) (b : β) [IsLin (λ p : X × Y => f p.1 p.2 a b)] (g : W → X) [IsLin g] (h : W → Y) [IsLin h]
         : IsLin (λ w => f (g w) (h w) a b) := sorry
-- ... This continues to infinity :( ... How to deal with these???



instance (f : Y → Z) [IsLin f] (g : X → Y) [IsLin g] : IsLin (f ∘ g) := sorry -- This does not seem to be infered from the above
instance : IsLin (λ x : X×X => x.1+x.2) := sorry

@[simp] def Function.comp_reduce {α β γ} (f : β → γ) (g : α → β) (a : α) : (f ∘ g) a = f (g a) := by simp

section Tests

  variable {α β γ : Type}

  variable (f : Y → Z) (g : X → Y) [IsLin f] [IsLin g] (h : X → X) [IsLin h] (h' : Y → Y) [IsLin h']
  variable (F : Y → α → X) (a : α) [IsLin (λ y => F y a)]
  variable (G : X → α → β → Y) (b : β) [IsLin (λ x => G x a b)]
  variable (H : α → X → β → Y) [IsLin (λ x => H a x b)]
  variable (H': α → β → X → Y) [IsLin (λ x => H' a b x)]

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
  def test17 (f : X → α → X → Y) (a : α) [IsLin (λ xx : X×X => f xx.1 a xx.2)] : IsLin (λ x => f x a x) := by infer_instance
  def test18 (f : X → α → X → Y) (a : α) [IsLin (λ xx : X×X => f xx.1 a xx.2)] : IsLin (λ x => f (h x) a x) := by infer_instance
  def test19 (f : X → X → Y) [IsLin (λ xx : X×X => f xx.1 xx.2)] : IsLin (λ x => f x (h x)) := by infer_instance
  def test20 : IsLin (λ (g : X → Y) (x : X) => F (g (h x)) a) := by infer_instance
  def test21 (f : X → α → X → Y) (a : α) [IsLin (λ xx : X×X => f xx.1 a xx.2)] : IsLin (λ x => f x a (h x)) := by infer_instance
  def test22 (f : X → α → X → Y) (a : α) [IsLin (λ xx : X×X => f xx.1 a xx.2)] : IsLin (λ x => f (h x) a (h x)) := by infer_instance
  def test23 (f : X → α → X → Y) (a : α) [IsLin (λ xx : X×X => f xx.1 a xx.2)] : IsLin (λ (h : X → X) x => f (h x) a (h x)) := by infer_instance
  def test24 : IsLin (λ (h : X → X) (x : X) => G (h x) a b) := by infer_instance
  def test25 : IsLin (λ (h : X → X) (x : X) => H a (h x) b) := by infer_instance
  def test26 : IsLin (λ (h : X → X) (x : X) => H' a b (h x)) := by infer_instance
  -- def test24 (f : X → X → α → Y) (a : α) [IsLin (λ xx : X×X => f xx.1 xx.2 a)] : IsLin (λ x => f (h x) x a) := by infer_instance

end Tests



namespace combtests
variable {α β γ : Type} 
variable {X : Type} {Y : Type} {Z : Type} [Vec X] [Vec Y] [Vec Z]

theorem test1 (f : X → X) [IsLin f] : IsLin ((f ∘ f) ∘ (f ∘ (f ∘ f))) := by infer_instance
theorem test2 (f : β → X → Y) (g : α → β) (a : α) [IsLin (f (g a))] : IsLin (comp f g a) := by infer_instance
theorem test3 (y : X) (A : X → X) (B : X → X) [IsLin A] [IsLin B] : IsLin λ x => (B∘A) x + B (A (B x) + B x) := by infer_instance
 
end combtests
