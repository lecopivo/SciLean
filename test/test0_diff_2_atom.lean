import SciLean.Core.Functions
-- import SciLean.Tactic.CustomSimp.DebugSimp
-- import SciLean.Tactic.AutoDiff.Main

-- namespace SciLean.Smooth
open SciLean
variable {α β γ : Type}
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]

set_option maxHeartbeats 500
set_option synthInstance.maxHeartbeats 160
set_option synthInstance.maxSize 30

--- Test 0 
-- We want to solve all these in a single pass i.e. linear complexity in the expression size
macro "diff_simp" : tactic => `(simp) -- `(autodiff_core (config := {singlePass := true}))

-- set_option trace.Meta.Tactic.simp true in
-- set_option trace.Meta.Tactic.simp.rewrite true in
example : δ (λ x : X×Y => x.fst) = λ x dx => dx.1 := by diff_simp --; simp only [AutoImpl.normalize_val]
example : δ (λ x : X×Y => x.2) = λ x dx => dx.2 := by diff_simp --; simp only [AutoImpl.normalize_val]
example : δ (λ x : X => - x) = λ x dx => (-dx : X) := by diff_simp --; simp only [AutoImpl.normalize_val]

example (x : X) : δ (λ r : ℝ => r * x) = λ r dr : ℝ => dr * x := by diff_simp --; simp only [AutoImpl.normalize_val];  done
example (r : ℝ) : δ (λ x : X => r * x) = λ x dx : X => r * dx := by diff_simp --; simp only [AutoImpl.normalize_val]
example (x : X) : δ (λ y : X => x + y) = λ y dy => dy := by diff_simp
example (y : X) : δ (λ x : X => x + y) = λ x dx => dx := by diff_simp --; simp only [add_zero];
example (x : X) : δ (λ y : X => x - y) = λ y dy => (-dy : X) := by diff_simp
example (y : X) : δ (λ x : X => x - y) = λ x dx => dx := by diff_simp --; simp only [AutoImpl.normalize_val]; simp;

example {X} [Hilbert X] (y : X) : δ (λ x : X => ⟪x, y⟫) = λ x dx => ⟪dx, y⟫ := by diff_simp
example {X} [Hilbert X] (y : X) : δ (λ x : X => ⟪x, y⟫) = λ x dx => ⟪dx, y⟫ := by diff_simp 
example {X} [Hilbert X] (x : X) : δ (λ y : X => ⟪x, y⟫) = λ y dy => ⟪x, dy⟫ := by diff_simp
example {ι} [Enumtype ι] : δ (λ f : ι → X => ∑ i, f i) = λ f df => ∑ i, df i := by diff_simp done
