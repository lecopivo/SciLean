import SciLean.Basic
import SciLean.Tactic

open SciLean

variable (f df : ℝ ⟿ ℝ)

example : δ (λ (f : (ℝ ⟿ ℝ)) => (∫ t, f t)) f df = ∫ t, df t := by
  simp[mkIntegral] done

set_option synthInstance.maxHeartbeats 5000
example : δ (λ (f : (ℝ ⟿ ℝ)) (t : ℝ) => (f t) * (f t)) f df = λ t => (df t) * (f t) + (f t) * (df t) :=
by
  autodiff done

example (t b : ℝ) : δ (fun (f : ℝ ⟿ ℝ) (t : ℝ) => (f t) * (f t)) f df t = (df t) * (f t) + (f t) * (df t) := by simp done
example (t : ℝ) : δ (fun (f : ℝ ⟿ ℝ) (t : ℝ) => (f t) * (f t)) f df t = (df t) * (f t) + (f t) * (df t) := by simp done 


set_option synthInstance.maxHeartbeats 50000
example : δ (λ (f : (ℝ ⟿ ℝ)) => (∫ t, (f t) * (f t))) f df = ∫ t, (df t) * (f t) + (f t) * (df t) := 
by
  simp[integral]
  simp[mkIntegral, integral]
  done

example : δ (λ (f : (ℝ ⟿ ℝ)) => (∫ t, (f t) * (f t) + (f t))) f df = ∫ t, (df t) * (f t) + (f t + 1) * (df t) := 
by
  simp[integral]
  simp[mkIntegral, integral]
  done
