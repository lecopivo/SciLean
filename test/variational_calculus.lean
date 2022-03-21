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


variable (f : ℝ ⟿ ℝ) (x : ℝ×ℝ)

#check δ (∫ t, f t)

class Dual (X Y : Type) where
  dual : (X → Y) → X


class Integral (X Y : Type) where
  Result : Type
  integral : X → Result

attribute [reducible] Integral.Result

-- def int {X Y} [FinVec X] [SemiHilbert Y] (f : X → Y) (Ω : 𝓓 (X ⟿ Y)) : Y := sorry

-- instance (priority := low) {X : Type} 

noncomputable
instance (priority := low) {X : Type} [SemiHilbert X] : Dual X (𝓓 X → ℝ) where
  dual := dual

noncomputable
instance [Hilbert X] : Dual X ℝ where
  dual := λ f => dual (λ x _ => f x)

#check Dual.dual (δ (λ x : ℝ×ℝ => ⟪x, 1⟫) x)
#check Dual.dual ((δ λ f : ℝ ⟿ ℝ => λ Ω => ⟪f, 1⟫[Ω]) f)

-- example : δ (λ (f : (ℝ ⟿ ℝ)) => (∫ t, (f t) * (f t) + (f t))) f df = ∫ t, (df t) * (f t) + (f t + 1) * (df t) := 
-- by
--   simp[integral]
--   simp[mkIntegral, integral]
--   done
