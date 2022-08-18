import SciLean.Data.PowType
-- import SciLean.Tactic.AutoDiff.Main

open SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]
variable {I : Type} [Enumtype I]

-- set_option maxHeartbeats 20000000
-- set_option synthInstance.maxHeartbeats 500000
-- set_option synthInstance.maxSize 2048

variable {n} [Fact (n≠0)]

example : Vec (ℝ^{n}) := by infer_instance
example : Vec (ℝ^I) := by infer_instance


-- This one is problematic. It clashes with this instance and it is 
-- the reason why the instance is marked local.
-- local instance (priority := low) [AddMonoid Y] [DistribMulAction ℝ Y] : DistribMulAction ℝ T := DistribMulAction.mk sorry sorry
example : ∀ (i : Fin n), IsSmooth λ (x : ℝ^{n}) => ∥x[i]∥² := by infer_instance -- apply λ i => SciLean.comp.arg_x.isSmooth
example : IsSmooth (λ (x : ℝ^{n}) => ∥x∥²) := by infer_instance
example : IsSmooth (λ (x : ℝ^{n}) => ⟪x,x⟫) := by infer_instance

example (i) : ∂ (λ (x : ℝ^{n}) => ∥x[i]∥²) = λ x dx => 2*⟪dx[i],x[i]⟫:= by simp
example : ∂ (λ (x : ℝ^{n}) (i : Fin n) => x[i]) = λ x dx i => dx[i] := by simp

section 
  -- variable {T Y : Type} [Hilbert Y] [FunType T (Fin n) Y] [FunType.HasIntro T] [FunType.HasSet T] [Fact (n≠0)]
example (h : Fin n) : ∂ (λ (x : ℝ^{n}) => ∑ i, ∥x[i+h]∥²) = λ x dx => ∑ i, 2*⟪dx[i+h],x[i+h]⟫ := by simp
example (h : Fin n) : ∂ (λ (x : ℝ^{n}) => ∑ i, ∥x[i+h] - x[i]∥²) = λ x dx => ∑ i, 2*⟪dx[i+h] - dx[i], x[i+h] - x[i]⟫ := by simp
end


variable {n : Nat} [Nonempty (Fin n)]

set_option trace.Meta.Tactic.simp.discharge true in
example : ∂ (λ x : ℝ^{n} => ∑ i, ∥x[i] - x[i - (1 : Fin n)]∥²) = 0 := by simp
