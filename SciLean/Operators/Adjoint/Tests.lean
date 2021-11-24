import SciLean.Basic
-- import SciLean.Simp
import SciLean.Tactic

set_option synthInstance.maxHeartbeats 5000

open Function

namespace SciLean.Adjoint.Tests

  variable {α β γ : Type}
  variable {X Y Z : Type} [Hilbert X] [Hilbert Y] [Hilbert Z]

  example (f g : X → Y) [IsLin f] [IsLin g] (y : Y) : (λ x => f x + g x)† y = f† y + g† y := by autoadjoint done
  example (y : Y) (r : ℝ) : (λ x => ⟨x,y⟩)† r = r*y := by autoadjoint done
  example (y : X) (r : ℝ) : (λ x => ⟨x,y⟩ + ⟨y,x⟩)† r = 2*r*y := by autoadjoint done
  example (r : ℝ) (x' : X) : (λ x : X => r*((λ x'' => ⟨x', x''⟩) x))† = λ s => r * s * x' := by autoadjoint done
  example : (λ (x : Fin n → ℝ) => sum λ i => x i)† 1 = (λ i => (1 : ℝ)) := by autoadjoint done
  example {n : Nat} (a : Fin n) [NonZero n] : (λ (f : Fin n → ℝ) i => f (i - a))† = (λ (f : Fin n → ℝ) x => f (x + a)) := by autoadjoint
  example {n} [NonZero n] (f : Fin n → ℝ) (c : Fin n) 
          : (λ (g : Fin n → ℝ) => sum (λ i => (f i) * (g (i+c))))† (1 : ℝ) = (fun i => f (i - c)) := by autoadjoint simp done
  example {n} [NonZero n] (f : Fin n → ℝ) (c : Fin n) 
          : (λ (g : Fin n → ℝ) => ⟨f, λ i => (g (i+c))⟩)† (1 : ℝ) = (fun i => f (i - c)) := by autoadjoint simp done
  example {n} [NonZero n] (c : Fin n) : (λ (g : Fin n → ℝ) => (λ i => g (i+c)))† = (fun f x => f (x - c)) := by autoadjoint done
