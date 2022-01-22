import SciLean.Basic
import SciLean.Tactic

set_option synthInstance.maxHeartbeats 5000

open SciLean

variable (f df : ℝ ⟿ ℝ)

-- TODO: Move this somewhere else ... 
@[simp high] theorem differential_of_hom_subtype {X Y} [Vec X] [Vec Y] : δ (Subtype.val : (X ⟿ Y) → (X → Y)) = λ f df => df.1 := sorry

example : δ (λ (f : (ℝ ⟿ ℝ)) => (∫ t, f t)) f df = ∫ t, df t := by
  simp[mkIntegral] done

example : δ (λ (f : (ℝ ⟿ ℝ)) (t : ℝ) => (f t) * (f t)) f df = λ t => (df t) * (f t) + (f t) * (df t) :=
by
  autodiff done

example (t b : ℝ) : δ (fun (f : ℝ ⟿ ℝ) (t : ℝ) => (f t) * (f t)) f df t = (df t) * (f t) + (f t) * (df t) := by simp done
example (t : ℝ) : δ (fun (f : ℝ ⟿ ℝ) (t : ℝ) => (f t) * (f t)) f df t = (df t) * (f t) + (f t) * (df t) := by simp done 

-- example : δ (λ (f : (ℝ ⟿ ℝ)) => (∫ t, (f t) * (f t))) f df = ∫ t, (df t) * (f t) + (f t) * (df t) := 
-- by
--   simp[integral]
--   simp[mkIntegral, integral]
--   done

-- example : δ (λ (f : (ℝ ⟿ ℝ)) => (∫ t, (f t) * (f t) + (f t))) f df = ∫ t, (df t) * (f t) + (f t + 1) * (df t) := 
-- by
--   simp[integral]
--   simp[mkIntegral, integral]
--   done


