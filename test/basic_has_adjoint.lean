import SciLean.Basic
import SciLean.Simp
import SciLean.Tactic

open Function

open SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
variable {U V W : Type} [Hilbert U] [Hilbert V] [Hilbert W]

example : HasAdjoint λ xx : X × X => xx.1 + xx.2 := by infer_instance
example : HasAdjoint λ uu : U × U => uu.1 + uu.2 := by infer_instance
example : HasAdjoint (λ x : ℝ × ℝ => x.1 + x.2) := by infer_instance
example : HasAdjoint (λ x : X × X => x.1 + x.2) := by infer_instance
example : HasAdjoint (λ x : U × U => x.1 + x.2) := by infer_instance

example {y : ℝ} : HasAdjoint (λ x : ℝ => y * x) := by infer_instance
example : ∀ y, HasAdjoint (λ x : ℝ => y * x) := by infer_instance
example {n} (f : Fin n → ℝ) (i) : HasAdjoint λ x => f i * x := by infer_instance
example {n} (f : Fin n → ℝ) : ∀ i, HasAdjoint λ x => f i * x := by infer_instance
example {ι} [Enumtype ι] (f : ι → ℝ) : HasAdjoint (λ (df : ι → ℝ) i => df i) := by infer_instance
example {n} [NonZero n] (f : Fin n → ℝ) (c : Fin n) : HasAdjoint fun (x : Fin n → ℝ) i => f i * x (i + c) := by infer_instance

example {ι} [Enumtype ι] (f : ι → ℝ) : HasAdjoint (λ (df : ι → ℝ) i => f i * df i) := by infer_instance done
set_option synthInstance.maxHeartbeats 1000 in
example {ι} [Enumtype ι] [Nonempty ι] (f : ι → ℝ) : HasAdjoint (λ (df : ι → ℝ) i => df i * f i + f i * df i) := by infer_instance done
example {ι} [Enumtype ι] (f : ι → ℝ) : HasAdjoint (λ (df : ι → ℝ) i => df i * f i) := by infer_instance done
example {n} [NonZero n] (f : Fin n → ℝ) : HasAdjoint (λ r i => (f i) * r) := by infer_instance done
set_option synthInstance.maxHeartbeats 2000 in
example {n} [NonZero n] (g : Fin n → ℝ) (c : Fin n) 
 : HasAdjoint (fun (df : Fin n → ℝ) => sum fun (b : Fin n) => df (b + c) * g c + g (b + c) * df b) := by infer_instance done

example {n} [NonZero n] (g : Fin n → ℝ) (c : Fin n) : HasAdjoint fun (f : Fin n → ℝ) (b : Fin n) => f c := by infer_instance
set_option synthInstance.maxHeartbeats 2000 in
example {n} [NonZero n] (g : Fin n → ℝ) (c : Fin n) : HasAdjoint fun (f : Fin n → ℝ) b => f (b + c) * g c + g (b + c) * f c := by infer_instance

example (x : Fin n → ℝ) (i : Fin n) : SciLean.HasAdjoint fun (dx : Fin n → ℝ) => ∑ j, x i * (dx i + dx j) := by infer_instance done
example {m : Nat} : ∀ (i : Fin n), HasAdjoint fun (dx : Fin n → ℝ^m) j => dx i + dx j := by infer_instance done
set_option synthInstance.maxHeartbeats 4000 in
example (x : Fin n → ℝ^(3:ℕ)) (i : Fin n) : SciLean.HasAdjoint fun (dx : Fin n → ℝ^(3:ℕ)) j => ⟪x i, dx j⟫ := by infer_instance done
set_option synthInstance.maxHeartbeats 2000 in
set_option synthInstance.maxSize 200 in
example {m : Nat} (x : ℝ^m) : ∀ (i : Fin n), HasAdjoint fun (dx : Fin n → ℝ^m) => ∑ j : Fin n, 2 * ⟪x, dx i + dx j⟫ := by infer_instance done

