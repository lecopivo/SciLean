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

example : Hilbert (ℝ × ℝ) := by infer_instance

example : SemiInner.Trait (ℝ × ℝ) := by infer_instance
example : SemiInner.Trait₂ ℝ ℝ := by infer_instance

open SemiInner in
example : SemiHilbert (ℝ × ℝ) (Trait₂.R ℝ ℝ) (Trait₂.D ℝ ℝ) (Trait₂.eval) := by infer_instance

-- set_option synthInstance.maxHeartbeats 50000 in
-- set_option trace.Meta.synthInstance true in
-- set_option trace.Meta.isDefEq true in
example : HasAdjoint (λ x : ℝ × ℝ => x.1 + x.2) := by
  apply (Adjoint.instHasAdjointProdHAdd)

-- set_option synthInstance.maxHeartbeats 5000 in
-- set_option trace.Meta.synthInstance true in
-- set_option trace.Meta.isDefEq true in
example : HasAdjoint (λ x : ℝ × ℝ => x.1 + x.2) := by infer_instance
example : HasAdjoint (λ x : X × X => x.1 + x.2) := by infer_instance
example : HasAdjoint (λ x : U × U => x.1 + x.2) := by infer_instance


