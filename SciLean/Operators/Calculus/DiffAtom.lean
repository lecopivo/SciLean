import SciLean.Operators.Calculus.DiffCore
import SciLean.Operators.Calculus.AtomicSmoothFun

namespace SciLean.Smooth

variable {α β γ : Type}
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]


@[reducible]
instance : AtomicSmoothFun (Prod.fst : X×Y → X) where
  df := λ x dx => dx.1
  is_smooth := sorry
  is_df := sorry

@[reducible]
instance : AtomicSmoothFun (Prod.snd : X×Y → Y) where
  df := λ x dx => dx.2
  is_smooth := sorry
  is_df := sorry

@[reducible]
instance : AtomicSmoothFun (Neg.neg : X → X) where
  df := λ x dx => - dx
  is_smooth := sorry
  is_df := sorry

@[reducible]
instance : AtomicSmoothFun₂ (HMul.hMul : ℝ → X → X) where
  df₁ := λ r dr x => dr * x
  df₂ := λ r x dx => r * dx
  is_smooth₁ := sorry
  is_smooth₂ := sorry
  is_df₁ := sorry
  is_df₂ := sorry


@[reducible]
instance : AtomicSmoothFun₂ (HAdd.hAdd : X → X → X) where
  df₁ := λ x dx y => dx
  df₂ := λ x y dy => dy
  is_smooth₁ := sorry
  is_smooth₂ := sorry
  is_df₁ := sorry
  is_df₂ := sorry

@[reducible]
instance : AtomicSmoothFun₂ (HSub.hSub : X → X → X) where
  df₁ := λ x dx y => dx
  df₂ := λ x y dy => - dy
  is_smooth₁ := sorry
  is_smooth₂ := sorry
  is_df₁ := sorry
  is_df₂ := sorry

@[reducible]
instance {X} [SemiHilbert X] : AtomicSmoothFun₂ (λ (x y : X) Ω => ⟪x, y⟫[Ω]) where
  df₁ := λ x dx y Ω => ⟪dx, y⟫[Ω]
  df₂ := λ x y dy Ω => ⟪x, dy⟫[Ω]
  is_smooth₁ := sorry
  is_smooth₂ := sorry
  is_df₁ := sorry
  is_df₂ := sorry

-- set_option trace.Meta.Tactic.simp.rewrite true in
@[reducible]
instance {X} [Hilbert X] : AtomicSmoothFun (λ x : X => ∥x∥²) where
  df := λ x dx => 2 * ⟪x, dx⟫
  is_smooth := by simp[SemiInner.normSqr] infer_instance done
  is_df := by simp [SemiInner.normSqr] simp_rw [SemiHilbert.semi_inner_sym] simp done

@[reducible]
instance {ι} [Enumtype ι] : AtomicSmoothFun (sum : (ι → X) → X) where
  df := λ f df => sum df
  is_smooth := sorry
  is_df := sorry
