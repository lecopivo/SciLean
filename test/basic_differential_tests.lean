import SciLean.Core.Functions
-- import SciLean.Tactic.AutoDiff.Main

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

-- macro "diff_simp" : tactic => `(autodiff_core (config := {singlePass := true}))
macro "diff_simp" : tactic => `(simp) -- `(autodiff_core (config := {singlePass := true}))

example : ∂ (λ x => x) x dx = dx := by diff_simp done
example : ∂ (λ x => f (g x)) x dx = ∂ f (g x) (∂ g x dx) := by diff_simp done
example : ∂ (λ x => f (g (f1 x))) x dx = ∂ f (g (f1 x)) (∂ g (f1 x) (∂ f1 x dx)) := by diff_simp done
example (y x dx : X) : ∂ (λ x : X => y) x dx = 0 := by diff_simp done
example : ∂ (λ x => x + x) x dx = dx + dx := by diff_simp done
example : ∂ (λ (x : X) => F x (g x)) x dx = ∂ F x dx (g x) + ∂ (F x) (g x) (∂ g x dx) := by diff_simp  done
example : ∂ (λ (x : X) => f3 (F x (g x))) x dx = ∂ f3 (F x (g x)) (∂ F x dx (g x) + ∂ (F x) (g x) (∂ g x dx)) := by diff_simp done
example g dg x : ∂ (λ (g : X → Y) => f (g x)) g dg = ∂ f (g x) (dg x) := by diff_simp done
example g dg x : ∂ (λ (g : X → Y) (x : X) => F x (g x)) g dg x = ∂ (F x) (g x) (dg x) := by diff_simp done
example g dg x : ∂ (λ (g : X → X) (y : Y) => F (g x) y) g dg y = ∂ F (g x) (dg x) y := by diff_simp done
example (r dr : ℝ) : ∂ (λ x : ℝ => x*x + x) r dr = dr * r + r * dr + dr := by diff_simp; done
example (r dr : ℝ) : ∂ (λ x : ℝ => x*x*x + x) r dr = (dr * r + r * dr) * r + r * r * dr + dr := by diff_simp; done
example g dg y : ∂ (λ (g : X → X) (x : X) => F (g x) y) g dg x = ∂ F (g x) (dg x) y := by diff_simp done 
