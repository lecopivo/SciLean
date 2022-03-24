import SciLean.Operators.Calculus.DiffAtom

namespace SciLean.Smooth

variable {α β γ : Type}
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]

set_option maxHeartbeats 1200
set_option synthInstance.maxHeartbeats 200
set_option synthInstance.maxSize 50


example (a : α) (f : Y → α → Z) [IsSmooth f] (g : X → Y) [IsSmooth g]
  : δ (λ x => f (g x) a) = λ x dx => δ f (g x) (δ g x dx) a := by simp

example (f : Y → Z) [IsSmooth f]
  : δ (λ (g : α → Y) (a : α) => f (g a)) = λ g dg a => δ f (g a) (dg a) := by simp

example
  : δ (λ (f : β → Z) (g : α → β) (a : α) => f (g a)) = λ f df (g : α → β) a => df (g a) := by simp

example (f : Y → β → Z) (g : X → Y) [IsSmooth f] [IsSmooth g] (b) 
  : δ (λ x => f (g x) b) = λ x dx => δ f (g x) (δ g x dx) b := by simp

example (f : Y → β → Z) [IsSmooth f] (b)
  : δ (λ (g : α → Y) a => f (g a) b) = λ g dg a => δ f (g a) (dg a) b := by simp

example (f : β → Y → Z) (g : β → X → Y) [∀ b, IsSmooth (f b)] [∀ b, IsSmooth (g b)]
  : δ (λ x b => f b (g b x)) = λ x dx b => δ (f b) (g b x) (δ (g b) x dx) := by simp

example (f : Y → β → Z) (g : X → Y) [IsSmooth f] [IsSmooth g]
  : δ (λ x b => f (g x) b) = λ x dx b => δ f (g x) (δ g x dx) b := by simp

example (f : Y → β → Z) [IsSmooth f]
  : δ (λ (g : α → Y) a b => f (g a) b) = λ g dg a b => δ f (g a) (dg a) b := by simp

example (f : Y₁ → β2 → Z) (g2 : α → β2) [IsSmooth f] (g dg)
  : δ (λ  (g1 : α → Y₁) a => f (g1 a) (g2 a)) g dg = λ a => δ f (g a) (dg a) (g2 a) := by simp

example (f : β1 → Y₂ → Z) (g1 : α → β1) [∀ y1, IsSmooth (f y1)] 
  : δ (λ (g2 : α → Y₂) a => f (g1 a) (g2 a)) = λ g dg a => δ (f (g1 a)) (g a) (dg a) := by simp

example (f : Y₁ → Y₂ → β → Z) (g1 : X → Y₁) (g2 : X → Y₂)
  [IsSmooth f] [∀ y1, IsSmooth (f y1)] [IsSmooth g1] [IsSmooth g2]
  : δ (λ (x : X) (b : β) => f (g1 x) (g2 x) b) = λ x dx b => δ f (g1 x) (δ g1 x dx) (g2 x) b + δ (f (g1 x)) (g2 x) (δ g2 x dx) b := by simp

example {X} [Hilbert X] : δ (λ x : X => ⟪x, x⟫) = λ x dx => 2 * ⟪dx, x⟫ :=
  by simp[AtomicSmoothFun₂.df₁, AtomicSmoothFun₂.df₂]
     simp_rw [SemiHilbert.semi_inner_sym] simp



--- Other a bit more disorganized tests

variable (f : Y → Z) [IsSmooth f]
variable (g : X → Y) [IsSmooth g]
variable (f1 : X → X) [IsSmooth f1]
variable (f2 : Y → Y) [IsSmooth f2]
variable (f3 : Z → Z) [IsSmooth f3]
variable (F : X → Y → Z) [IsSmooth F] [∀ x, IsSmooth (F x)]
variable (G : X × Y → Z) [IsSmooth G]

variable (x dx : X) (y dy : Y) (z dz : Z)

example : δ (λ x => f (g (f1 x))) x dx = δ f (g (f1 x)) (δ g (f1 x) (δ f1 x dx)) := by simp done
example : δ (λ x => x + x) x dx = dx + dx := by simp done

example : δ (λ (x : X) => F x (g x)) x dx = δ F x dx (g x) + δ (F x) (g x) (δ g x dx) := by simp  done
example : δ (λ (x : X) => f3 (F x (g x))) x dx = δ f3 (F x (g x)) (δ F x dx (g x) + δ (F x) (g x) (δ g x dx)) := by simp done
example g dg x : δ (λ (g : X → Y) => f (g x)) g dg = δ f (g x) (dg x) := by simp done
example g dg x : δ (λ (g : X → Y) (x : X) => F x (g x)) g dg x = δ (F x) (g x) (dg x) := by simp done
example g dg x : δ (λ (g : X → X) (y : Y) => F (g x) y) g dg y = δ F (g x) (dg x) y := by simp done
example (r dr : ℝ) : δ (λ x : ℝ => x*x + x) r dr = dr*r + (r + 1)*dr := by simp done
example g dg y : δ (λ (g : X → X) (x : X) => F (g x) y) g dg x = δ F (g x) (dg x) y := by simp done 

set_option synthInstance.maxHeartbeats 300 in
set_option maxHeartbeats 2500 in
example (r dr : ℝ) : δ (λ x : ℝ => x*x*x + x) r dr = (dr * r + r * dr) * r + (r * r + 1) * dr := by simp done
