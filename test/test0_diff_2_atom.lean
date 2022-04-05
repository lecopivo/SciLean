import SciLean.Operators.Calculus.DiffAtom

namespace SciLean.Smooth

variable {α β γ : Type}
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]

set_option maxHeartbeats 500
set_option synthInstance.maxHeartbeats 160
set_option synthInstance.maxSize 30

--- Test 0 

example : δ (λ x : X×Y => x.1) = λ x dx => dx.1 := by simp
example : δ (λ x : X×Y => x.2) = λ x dx => dx.2 := by simp
example : δ (λ x : X => - x) = λ x dx => (-dx : X) := by simp
example (x : X) : δ (λ r : ℝ => r * x) = λ r dr : ℝ => dr * x := by simp
example (r : ℝ) : δ (λ x : X => r * x) = λ x dx : X => r * dx := by simp
example (x : X) : δ (λ y : X => x + y) = λ y dy => dy := by simp
example (y : X) : δ (λ x : X => x + y) = λ x dx => dx := by simp done
example (x : X) : δ (λ y : X => x - y) = λ y dy => (-dy : X) := by simp
example (y : X) : δ (λ x : X => x - y) = λ x dx => dx := by simp done
example {X} [SemiHilbert X] (y : X) Ω : δ (λ x : X => ⟪x, y⟫[Ω]) = λ x dx => ⟪dx, y⟫[Ω] := by simp done
example {X} [SemiHilbert X] (x : X) Ω : δ (λ y : X => ⟪x, y⟫[Ω]) = λ y dy => ⟪x, dy⟫[Ω] := by simp done
example {ι} [Enumtype ι] : δ (λ f : ι → X => ∑ i, f i) = λ f df => ∑ i, df i := by simp done


