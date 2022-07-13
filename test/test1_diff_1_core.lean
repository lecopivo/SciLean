import SciLean.Core.Functions
-- import SciLean.Tactic.AutoDiff.Main

namespace SciLean.Smooth

variable {α β γ : Type}
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]

set_option maxHeartbeats 2000
set_option synthInstance.maxHeartbeats 250
set_option synthInstance.maxSize 60

-- macro "diff_simp" : tactic => `(autodiff_core (config := {singlePass := true}))
macro "diff_simp" : tactic => `(simp) 

example (a : α) (f : Y → α → Z) [IsSmooth f] (g : X → Y) [IsSmooth g]
  : ∂ (λ x => f (g x) a) = λ x dx => ∂ f (g x) (∂ g x dx) a := by diff_simp

example (f : Y → Z) [IsSmooth f]
  : ∂ (λ (g : α → Y) (a : α) => f (g a)) = λ g dg a => ∂ f (g a) (dg a) := by diff_simp

example
  : ∂ (λ (f : β → Z) (g : α → β) (a : α) => f (g a)) = λ f df (g : α → β) a => df (g a) := by diff_simp

example (f : Y → β → Z) (g : X → Y) [IsSmooth f] [IsSmooth g] (b) 
  : ∂ (λ x => f (g x) b) = λ x dx => ∂ f (g x) (∂ g x dx) b := by diff_simp

example (f : Y → β → Z) [IsSmooth f] (b)
  : ∂ (λ (g : α → Y) a => f (g a) b) = λ g dg a => ∂ f (g a) (dg a) b := by diff_simp

example (f : β → Y → Z) (g : β → X → Y) [∀ b, IsSmooth (f b)] [∀ b, IsSmooth (g b)]
  : ∂ (λ x b => f b (g b x)) = λ x dx b => ∂ (f b) (g b x) (∂ (g b) x dx) := by diff_simp

example (f : Y → β → Z) (g : X → Y) [IsSmooth f] [IsSmooth g]
  : ∂ (λ x b => f (g x) b) = λ x dx b => ∂ f (g x) (∂ g x dx) b := by diff_simp

example (f : Y → β → Z) [IsSmooth f]
  : ∂ (λ (g : α → Y) a b => f (g a) b) = λ g dg a b => ∂ f (g a) (dg a) b := by diff_simp

example (f : Y₁ → β2 → Z) (g2 : α → β2) [IsSmooth f] (g dg)
  : ∂ (λ  (g1 : α → Y₁) a => f (g1 a) (g2 a)) g dg = λ a => ∂ f (g a) (dg a) (g2 a) := by diff_simp

example (f : β1 → Y₂ → Z) (g1 : α → β1) [∀ y1, IsSmooth (f y1)] 
  : ∂ (λ (g2 : α → Y₂) a => f (g1 a) (g2 a)) = λ g dg a => ∂ (f (g1 a)) (g a) (dg a) := by diff_simp

example (f : Y₁ → Y₂ → β → Z) (g1 : X → Y₁) (g2 : X → Y₂)
  [IsSmooth f] [∀ y1, IsSmooth (f y1)] [IsSmooth g1] [IsSmooth g2]
  : ∂ (λ (x : X) (b : β) => f (g1 x) (g2 x) b) = λ x dx b => ∂ f (g1 x) (∂ g1 x dx) (g2 x) b + ∂ (f (g1 x)) (g2 x) (∂ g2 x dx) b := by diff_simp

example {X} [Hilbert X] : ∂ (λ x : X => ⟪x, x⟫) = λ x dx =>  ⟪dx, x⟫ + ⟪x, dx⟫ := by diff_simp; done


--- Other a bit more disorganized tests

variable (f : Y → Z) [IsSmooth f]
variable (g : X → Y) [IsSmooth g]
variable (f1 : X → X) [IsSmooth f1]
variable (f2 : Y → Y) [IsSmooth f2]
variable (f3 : Z → Z) [IsSmooth f3]
variable (F : X → Y → Z) [IsSmooth F] [∀ x, IsSmooth (F x)]
variable (G : X × Y → Z) [IsSmooth G]

variable (x dx : X) (y dy : Y) (z dz : Z)

example : ∂ (λ x => f (g (f1 x))) x dx = ∂ f (g (f1 x)) (∂ g (f1 x) (∂ f1 x dx)) := by diff_simp done
example : ∂ (λ x => x + x) x dx = dx + dx := by diff_simp done

example : ∂ (λ (x : X) => F x (g x)) x dx = ∂ F x dx (g x) + ∂ (F x) (g x) (∂ g x dx) := by diff_simp  done
example : ∂ (λ (x : X) => f3 (F x (g x))) x dx = ∂ f3 (F x (g x)) (∂ F x dx (g x) + ∂ (F x) (g x) (∂ g x dx)) := by diff_simp done
example g dg x : ∂ (λ (g : X → Y) => f (g x)) g dg = ∂ f (g x) (dg x) := by diff_simp done
example g dg x : ∂ (λ (g : X → Y) (x : X) => F x (g x)) g dg x = ∂ (F x) (g x) (dg x) := by diff_simp done
example g dg x : ∂ (λ (g : X → X) (y : Y) => F (g x) y) g dg y = ∂ F (g x) (dg x) y := by diff_simp done
example (r dr : ℝ) : ∂ (λ x : ℝ => x*x + x) r dr = dr * r + r * dr + dr := by diff_simp; done
example g dg y : ∂ (λ (g : X → X) (x : X) => F (g x) y) g dg x = ∂ F (g x) (dg x) y := by diff_simp done 
example (r dr : ℝ) : ∂ (λ x : ℝ => x*x*x + x) r dr = (dr * r + r * dr) * r + r * r * dr + dr := by diff_simp; done
