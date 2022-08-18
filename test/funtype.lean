import SciLean.Core
import SciLean.Data.FunType
-- import SciLean.Tactic.AutoDiff.Main

open SciLean

variable {α β γ : Type}
variable {T X Y Z : Type} [Enumtype X] [Hilbert Y] [FunType T X Y] [FunType.HasIntro T] [FunType.HasSet T] [Vec Z]
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]

-- set_option maxHeartbeats 20000000
-- set_option synthInstance.maxHeartbeats 500000
-- set_option synthInstance.maxSize 2048

-- This one is problematic. It clashes with this instance and it is 
-- the reason why the instance is marked local.
-- local instance (priority := low-1) [AddCommMonoid Y] [DistribMulAction ℝ Y] : Module ℝ T := Module.mk
example : ∀ (i : X), IsSmooth λ (x : T) => ∥x[i]∥² := by infer_instance -- apply λ i => SciLean.comp.arg_x.isSmooth

example : ∀ (i : X), IsSmooth λ (x : T) => x[i] := by infer_instance
example (h : α → X) : IsSmooth (λ (x : T) (a : α) => x[h a]) := by infer_instance
example : IsSmooth (λ (x : T) => ∥x∥²) := by infer_instance
example : IsSmooth (λ (x : T) => ⟪x,x⟫) := by infer_instance
example (f : Y → Z) [IsSmooth f] : ∀ (i : X), IsSmooth λ (x : T) => f x[i] := by infer_instance
example (i : X) : IsSmooth λ (x : T) => ∥x[i]∥² := by infer_instance
example (i : X) : ∂ (λ (x : T) => x[i]) = λ (_ dx : T) => dx[i] := by simp
example (i) : ∂ (λ (x : T) => ∥x[i]∥²) = λ x dx => 2*⟪dx[i],x[i]⟫:= by simp
example : ∂ (λ (x : T) (i : X) => x[i]) = λ x dx i => dx[i] := by simp
example (h : α → X) : ∂ (λ (x : T) (a : α) => x[h a]) = λ x dx a => dx[h a] := by simp
example : ∂ (λ (x : T) => ∑ i, x[i]) = λ x dx => ∑ i, dx[i] := by simp
example : ∂ (λ (x : T) => ∑ i, ∥x[i]∥²) = λ x dx => ∑ i, 2*⟪dx[i],x[i]⟫ := by simp

section 
  variable {T Y : Type} [Hilbert Y] [FunType T (Fin n) Y] [FunType.HasIntro T] [FunType.HasSet T] [Fact (n≠0)]
  example (h : Fin n) : ∂ (λ (x : T) => ∑ i, ∥x[i+h]∥²) = λ x dx => ∑ i, 2*⟪dx[i+h],x[i+h]⟫ := by simp
  example (h : Fin n) : ∂ (λ (x : T) => ∑ i, ∥x[i+h] - x[i]∥²) = λ x dx => ∑ i, 2*⟪dx[i+h] - dx[i], x[i+h] - x[i]⟫ := by simp
end 

example : ∂† (λ (x : T) => ∑ i, ∥x[i]∥²) = λ x dx' => FunType.map (2*dx'*·) x := by simp
