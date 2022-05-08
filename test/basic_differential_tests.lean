import SciLean.Core.Functions

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]

variable (f : Y → Z) [IsSmooth f]
variable (g : X → Y) [IsSmooth g]
variable (f1 : X → X) [IsSmooth f1]
variable (f2 : Y → Y) [IsSmooth f2]
variable (f3 : Z → Z) [IsSmooth f3]
variable (F : X → Y → Z) [IsSmooth F] [∀ x, IsSmooth (F x)]
variable (G : X × Y → Z) [IsSmooth G]

variable (x dx : X) (y dy : Y) (z dz : Z)

example : δ (λ x => x) x dx = dx := by simp done
example : δ (λ x => f (g x)) x dx = δ f (g x) (δ g x dx) := by simp done
example : δ (λ x => f (g (f1 x))) x dx = δ f (g (f1 x)) (δ g (f1 x) (δ f1 x dx)) := by simp done
example (y x dx : X) : δ (λ x : X => y) x dx = 0 := by simp done
example : δ (λ x => x + x) x dx = dx + dx := by simp done

example : δ (λ (x : X) => F x (g x)) x dx = δ F x dx (g x) + δ (F x) (g x) (δ g x dx) := by simp  done
example : δ (λ (x : X) => f3 (F x (g x))) x dx = δ f3 (F x (g x)) (δ F x dx (g x) + δ (F x) (g x) (δ g x dx)) := by simp done
example g dg x : δ (λ (g : X → Y) => f (g x)) g dg = δ f (g x) (dg x) := by simp done
example g dg x : δ (λ (g : X → Y) (x : X) => F x (g x)) g dg x = δ (F x) (g x) (dg x) := by simp done
example g dg x : δ (λ (g : X → X) (y : Y) => F (g x) y) g dg y = δ F (g x) (dg x) y := by simp done
example (r dr : ℝ) : δ (λ x : ℝ => x*x + x) r dr = dr * r + r * dr + dr := by simp; ring done
example (r dr : ℝ) : δ (λ x : ℝ => x*x*x + x) r dr = (dr * r + r * dr) * r + r * r * dr + dr := by simp; ring done
example g dg y : δ (λ (g : X → X) (x : X) => F (g x) y) g dg x = δ F (g x) (dg x) y := by simp done 
