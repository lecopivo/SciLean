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


#check (λ x : ℝ => ∥x∥)

instance {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : X → Y → Z) (x dx : X) [IsSmooth f] [h : ∀ x, IsSmooth (f x)] : IsSmooth (δ f x dx) := sorry

@[simp] 
theorem diff_hoho {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : X → Y → Z) (x dx : X) [IsSmooth f] [h : ∀ x, IsSmooth (f x)] 
  : δ (λ x => (⟨f x, h x⟩ : Y ⟿ Z)) x dx = (⟨δ f x dx, by infer_instance⟩ : Y ⟿ Z) := sorry

example : δ (λ (f : (ℝ ⟿ ℝ)) => (∫ t, (f t) * (f t))) f df = ∫ t, (df t) * (f t) + (f t) * (df t) := 
by
  simp[integral]
  simp[mkIntegral, integral]
  done

-- instance : IsLin (⟪·, ·⟫ : ℝ → ℝ → ℝ) := sorry
-- instance (a) : IsLin (⟪a, ·⟫ : ℝ → ℝ) := sorry


example (t b : ℝ) : δ (fun (f : ℝ ⟿ ℝ) (t : ℝ) => ⟪(δ f.1 t 1), (δ f.1 t 1)⟫) f df t = 0 --(df t) * (f t) + (f t) * (df t) := by simp done
:= 
by
  simp
  done 

example (t : ℝ) : δ (fun (f : ℝ ⟿ ℝ) (t : ℝ) => (f t) * (f t)) f df t = (df t) * (f t) + (f t) * (df t) := by simp done

-- set_option maxHeartbeats 1000000

-- set_option trace.Meta.whnf true in
example : δ (λ (f : (ℝ ⟿ ℝ)) => (∫ t, (f t) * (f t) + (f t))) f df = ∫ t, (df t) * (f t) + (f t + 1) * (df t) := 
by
  simp[integral]
  simp[mkIntegral, integral]
  done
