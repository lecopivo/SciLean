import SciLean.Basic
-- import SciLean.Simp
import SciLean.Tactic

open SciLean

set_option synthInstance.maxHeartbeats 50000
-- set_option maxHeartbeats 500000

variable (f df : ℝ ⟿ ℝ)

example : δ (λ (f : (ℝ ⟿ ℝ)) => (∫ t, f t)) f df = ∫ t, df t := by
  simp[mkIntegral] done

example : δ (λ (f : (ℝ ⟿ ℝ)) (t : ℝ) => (f t) * (f t)) f df = λ t => (df t) * (f t) + (f t) * (df t) :=
by
  autodiff done

set_option maxHeartbeats 100000


example : δ (λ (f : (ℝ ⟿ ℝ)) => (∫ t, (f t) * (f t))) f df = ∫ t, (df t) * (f t) + (f t) * (df t) := 
by
  simp[integral]
  simp[mkIntegral, integral]
  done


example (t b : ℝ) : δ (fun (f : ℝ ⟿ ℝ) (t : ℝ) => (f t) * (f t)) f df t = (df t) * (f t) + (f t) * (df t) := by simp done

example (t : ℝ) : δ (fun (f : ℝ ⟿ ℝ) (t : ℝ) => (f t) * (f t)) f df t = (df t) * (f t) + (f t) * (df t) := by simp done 

-- set_option maxHeartbeats 1000000

-- set_option trace.Meta.whnf true in

-- This one is tooo slow
-- example : δ (λ (f : (ℝ ⟿ ℝ)) => (∫ t, (f t) * (f t) + (f t))) f df = ∫ t, (df t) * (f t) + (f t + 1) * (df t) := 
-- by
--   simp[integral]
--   simp[mkIntegral, integral]
--   done
