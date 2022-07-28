import SciLean.Core.Mor
import SciLean.Core.Fun

namespace SciLean

-- Sum --
---------

function_properties sum {ι X : Type} [Enumtype ι] (f : ι → X) : X
argument f [Vec X]
  isSmooth    := sorry,
  isLin       := sorry,
  diff_simp   := sum df by sorry
argument f [SemiHilbert X]
  hasAdjoint  := sorry,
  adj_simp    := λ _ => f' by sorry,
  hasAdjDiff  := by constructor; infer_instance; simp; infer_instance done,
  adjDiff_simp := λ _ => df' by simp[adjDiff] done


--- Sum simplifications ---
---------------------------
-- These theorems probably should not be under `simp` but under specialized tactic
-- For now, they are under `simp` to get some nice examples working

-- @[simp] 
theorem sum_of_const {X ι} [Enumtype ι] [Vec X] (x : X)
  : (∑ i : ι, x) = (Enumtype.numOf ι : ℝ) * x
  := sorry

-- @[simp] 
theorem sum_into_lambda {X Y ι} [Enumtype ι] [Vec Y]
  (f : ι → X → Y)
  : (∑ i, λ x => f i x) = (λ x => ∑ i, f i x)
  := sorry

-- @[simp] 
theorem sum_of_add {X ι} [Enumtype ι] [Vec X]
  (f g : ι → X)
  : (∑ i, f i + g i) = (∑ i, f i) + (∑ i, g i)
  := sorry

-- @[simp] 
theorem sum_of_sub {X ι} [Enumtype ι] [Vec X]
  (f g : ι → X)
  : (∑ i, f i - g i) = (∑ i, f i) - (∑ i, g i)
  := sorry

-- @[simp] 
theorem sum_of_smul {X ι} [Enumtype ι] [Vec X]
  (f : ι → X) (c : ℝ)
  : (∑ i, c * f i ) = c * (∑ i, f i)
  := sorry

-- @[simp]
theorem sum_of_neg {X ι} [Enumtype ι] [Vec X]
  (f : ι → X)
  : (∑ i, - f i ) = - (∑ i, f i)
  := sorry

-- @[simp low]
-- This can loop together with `sum_into_lambda`
theorem sum_of_linear {X Y ι} [Enumtype ι] [Vec X] [Vec Y]
  (f : X → Y) [IsLin f]
  (g : ι → X)
  : (∑ i, f (g i)) = f (∑ i, g i)
  := sorry

@[simp] 
theorem eval_of_sum {X ι α : Type} [Enumtype ι] [Vec X] (f : ι → α → X) (a : α)
  : (∑ i, f i) a = ∑ i, (f i a) :=
by 
  simp[← sum_of_linear (λ (g : α → X) => g a)]
  done
