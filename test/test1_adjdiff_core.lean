import SciLean.Core.Functions
-- import SciLean.Tactic.AutoDiff.Main

namespace SciLean.Smooth

variable {α β γ : Type}
variable {X Y Z W : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] [SemiHilbert W]
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]
variable {ι κ : Type} [Enumtype ι] [Enumtype κ] [Nonempty ι] [Nonempty κ]

-- macro "diff_simp" : tactic => `(autodiff_core (config := {singlePass := true}))
macro "diff_simp" : tactic => `(simp) -- `(autodiff_core (config := {singlePass := true}))


example {X} [Hilbert X] (x : X) : δ† (λ r : ℝ => r * x) = λ r dr' => ⟪dr', x⟫ := by diff_simp
example (r : ℝ) : δ† (λ x : X => r * x) = λ x (dx' : X) => r * dx' := by diff_simp
example : δ† (λ x : ℝ => x * x) = λ x dx' : ℝ => dx' * x + x * dx' := by diff_simp

example : δ† (λ (x : X) (i : ι) => x) = λ x dx' => ∑ i, dx' i := by diff_simp
example : δ† (λ (f : ι → X) (i : ι) => f i) = λ f df' => df' := by diff_simp
example : δ† (λ (f : ι → X) (i : ι) => f) = λ f df' => ∑ j, df' j := by diff_simp

example (f : X → X → ℝ) [IsSmooth f] [∀ y, HasAdjDiff (λ x => f x y)] [∀ x, HasAdjDiff (λ y => f x y)]
  : δ† (λ (x : ι → X) => ∑ i j, f (x i) (x j)) 
    =
    (λ x dx' i=>
      (∑ j, δ† (λ y => f y (x j)) (x i) dx') + 
            δ† (λ y => f (x j) y) (x i) dx') := 
by 
  diff_simp; simp[sum_into_lambda]; admit


set_option trace.Meta.Tactic.simp.rewrite true in
set_option trace.Meta.Tactic.simp.discharge true in
example (α : Type) (a : α) (f : X → X → α → ℝ) [IsSmooth λ x y => f x y a] [∀ y, HasAdjDiff (λ x => f x y a)] [∀ x, HasAdjDiff (λ y => f x y a)]
  : δ† (λ (x : ι → X) => ∑ i j, f (x i) (x j) a) = 0 :=
by
  diff_simp; simp[sum_into_lambda];

set_option trace.Meta.Tactic.simp.rewrite true in
example (f : Y → ι → Z) [HasAdjDiff f] (g : X → Y) [HasAdjDiff g]
  : δ† (λ x i => f (g x) i) = λ x (dx' : ι → Z) => (δ† g x) (δ† f (g x) dx') := by diff_simp
