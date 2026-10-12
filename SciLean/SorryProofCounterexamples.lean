module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Counterexamples to two remaining `sorry_proof` goals

* `integral_zero_hausdof_of_singleton_inter_set_false`: the lemma
  `SciLean.integral_zero_hausdof_of_singleton_inter_set`
  (`SciLean/Analysis/Calculus/HasParamDerivWithDisc/Common.lean`) is false as stated. It does not
  assume that `Y` is complete, and the Bochner integral of every function into an incomplete space
  is `0`. The counterexample uses `Y = polynomialFunctionsOnUnitInterval`, the polynomial functions
  on `[0,1]` with the sup norm, which is not complete (`not_completeSpace_polynomialFunctions`).
* `bubblesort_decreasing_goal_false`: the goal left to `decreasing_by sorry_proof` in
  `List.bubblesort` (`SciLean/Modules/FiniteElement/Mesh/PrismRepr.lean`) is false, so that
  `sorry_proof` cannot be replaced without changing the termination measure.

This file is not imported by `SciLean.lean`.
-/

@[expose] public section

namespace SciLean.SorryProofCounterexamples

open MeasureTheory Polynomial

/-! ## An incomplete normed space -/

/-- The polynomial functions on `[0,1]`, as a real subspace of `C([0,1], ℝ)` with the sup norm. -/
noncomputable abbrev polynomialFunctionsOnUnitInterval : Submodule ℝ C(unitInterval, ℝ) :=
  Subalgebra.toSubmodule (polynomialFunctions (Set.Icc (0 : ℝ) 1))

/-- `x ↦ |x - 1/2|` on `[0,1]` is not a polynomial function. -/
theorem abs_sub_half_not_mem_polynomialFunctions :
    (⟨fun x : unitInterval => |(x : ℝ) - 1 / 2|, by fun_prop⟩ : C(unitInterval, ℝ)) ∉
      polynomialFunctions (Set.Icc (0 : ℝ) 1) := by
  intro hmem
  obtain ⟨p, -, hp⟩ := Subalgebra.mem_map.mp hmem
  have heval : ∀ x : unitInterval, p.eval (x : ℝ) = |(x : ℝ) - 1 / 2| := fun x => by
    have := congrArg (fun g : C(unitInterval, ℝ) => g x) hp
    simpa using this
  have hpq : p = X - C (1 / 2) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.Infinite.mono (s := Set.Icc (1 / 2 : ℝ) 1)
    · intro x hx
      have := heval ⟨x, by constructor <;> linarith [hx.1, hx.2]⟩
      simp only [Set.mem_ofPred_eq, eval_sub, eval_X, eval_C]
      rw [this]
      exact abs_of_nonneg (by linarith [hx.1])
    · exact Set.Icc_infinite (by norm_num)
  have h0 := heval ⟨0, by simp⟩
  rw [hpq] at h0
  norm_num at h0

/-- The polynomial functions on `[0,1]` with the sup norm are not complete. -/
theorem not_completeSpace_polynomialFunctions :
    ¬ CompleteSpace polynomialFunctionsOnUnitInterval := by
  intro h
  have hc : IsClosed (polynomialFunctionsOnUnitInterval : Set C(unitInterval, ℝ)) :=
    (completeSpace_coe_iff_isComplete.mp h).isClosed
  apply abs_sub_half_not_mem_polynomialFunctions
  have hc' : IsClosed ((polynomialFunctions (Set.Icc (0 : ℝ) 1)) : Set C(unitInterval, ℝ)) := hc
  have hg : (⟨fun x : unitInterval => |(x : ℝ) - 1 / 2|, by fun_prop⟩ : C(unitInterval, ℝ)) ∈
      (polynomialFunctions (Set.Icc (0 : ℝ) 1)).topologicalClosure := by
    rw [polynomialFunctions_closure_eq_top 0 1]
    exact Algebra.mem_top
  rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe, hc'.closure_eq] at hg
  exact hg

/-! ## `integral_zero_hausdof_of_singleton_inter_set` -/

/-- The statement of `SciLean.integral_zero_hausdof_of_singleton_inter_set` with `α = ℝ` and
`Y = polynomialFunctionsOnUnitInterval` is false: for the constant function `1`, `a = 0` and
`A = univ` the left side is `0` (the integral of a function into an incomplete space) and the right
side is `1 ≠ 0`. -/
theorem integral_zero_hausdof_of_singleton_inter_set_false :
    ¬ ∀ (f : ℝ → polynomialFunctionsOnUnitInterval) (a : ℝ) (A : Set ℝ) [Decidable (a ∈ A)],
      ∫ x in {a} ∩ A, f x ∂μH[0] = if a ∈ A then f a else 0 := by
  classical
  intro h
  let y : polynomialFunctionsOnUnitInterval := ⟨1, Subalgebra.one_mem _⟩
  have h1 := h (fun _ => y) 0 Set.univ
  have h0 : ∫ _ in {(0 : ℝ)} ∩ Set.univ, y ∂μH[0] = 0 :=
    integral_of_not_completeSpace not_completeSpace_polynomialFunctions
  rw [h0] at h1
  simp only [Set.mem_univ, ↓reduceIte] at h1
  have h2 := congrArg (fun g : polynomialFunctionsOnUnitInterval => (g : C(unitInterval, ℝ)) 0) h1
  simp [y] at h2

/-! ## `decreasing_by` of `List.bubblesort` -/

/-- The goal of `decreasing_by sorry_proof` in `List.bubblesort`, taken verbatim from the error
message (context `h`, `y < x`, `this`), is false: for `x = 1`, `xs = [0, 0]`, `y = 0`, `ys = [100]`
all hypotheses hold but `sizeOf (x :: ys) = 104` and `sizeOf (x :: xs) = 5`. -/
theorem bubblesort_decreasing_goal_false :
    ¬ ∀ (x : ℕ) (xs : List ℕ) (y : ℕ) (ys : List ℕ),
      xs.length = (y :: ys).length → y < x → ys.length.succ < xs.length.succ →
      sizeOf (x :: ys) < sizeOf (x :: xs) := by
  intro h
  exact absurd (h 1 [0, 0] 0 [100] rfl (by decide) (by decide)) (by decide)

end SciLean.SorryProofCounterexamples
