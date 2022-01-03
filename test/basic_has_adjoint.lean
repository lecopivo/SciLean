import SciLean.Basic
import SciLean.Simp
import SciLean.Tactic

open Function

open SciLean


variable {α β γ : Type}
variable {X Y Z : Type} {R D e} [Vec R] [SemiHilbert X R D e] [SemiHilbert Y R D e] [SemiHilbert Z R D e]
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
set_option synthInstance.maxHeartbeats 2000 
example {ι} [Enumtype ι] (f : ι → ℝ) : HasAdjoint (λ (df : ι → ℝ) i => df i * f i + f i * df i) := by infer_instance done
example {ι} [Enumtype ι] (f : ι → ℝ) : HasAdjoint (λ (df : ι → ℝ) i => df i * f i) := by infer_instance done
example {n} [NonZero n] (f : Fin n → ℝ) : HasAdjoint (λ r i => (f i) * r) := by infer_instance done
example {n} [NonZero n] (g : Fin n → ℝ) (c : Fin n) 
 : HasAdjoint (fun (df : Fin n → ℝ) => sum fun (b : Fin n) => df (b + c) * g c + g (b + c) * df b) := by infer_instance done

set_option synthInstance.maxHeartbeats 5000 
-- TODO: make these work!
-- example {n} [NonZero n] (g : Fin n → ℝ) (c : Fin n) : HasAdjoint fun (f : Fin n → ℝ) (b : Fin n) => f c := by infer_instance
-- example {n} [NonZero n] (g : Fin n → ℝ) (c : Fin n) : HasAdjoint fun (f : Fin n → ℝ) b => f (b + c) * g c + g (b + c) * f c := by infer_instance

