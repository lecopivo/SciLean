import SciLean.Operators.Calculus.DiffCore
import SciLean.Operators.Calculus.AtomicSmoothFun

namespace SciLean.Smooth

variable {α β γ : Type}
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]


-- @[reducible]
-- instance : AtomicSmoothFun (Prod.fst : X×Y → X) where
--   df := λ x dx => dx.1
--   is_smooth := sorry
--   is_df := sorry

instance : IsSmooth (Prod.fst : X×Y → X) := sorry
@[simp, diff]
theorem differential_of_fst : δ (λ ((x,y) : X×Y) => x) = λ (x,y) (dx,dy) => dx := sorry

-- @[reducible]
-- instance : AtomicSmoothFun (Prod.snd : X×Y → Y) where
--   df := λ x dx => dx.2
--   is_smooth := sorry
--   is_df := sorry

instance : IsSmooth (Prod.snd : X×Y → Y) := sorry
@[simp, diff]
theorem differential_of_snd : δ (λ ((x,y) : X×Y) => y) = λ (x,y) (dx,dy) => dy := sorry

-- @[reducible]
-- instance : AtomicSmoothFun (Neg.neg : X → X) where
--   df := λ x dx => - dx
--   is_smooth := sorry
--   is_df := sorry

instance : IsSmooth (Neg.neg : X → X) := sorry
@[simp, diff]
theorem differential_of_neg : δ (Neg.neg : X → X) = λ x dx : X => -dx := sorry

-- @[reducible]
-- instance : AtomicSmoothFun₂ (HMul.hMul : ℝ → X → X) where
--   df₁ := λ r dr x => dr * x
--   df₂ := λ r x dx => r * dx
--   is_smooth₁ := sorry
--   is_smooth₂ := sorry
--   is_df₁ := sorry
--   is_df₂ := sorry

instance : IsSmooth (HMul.hMul : ℝ → X → X) := sorry
instance (r : ℝ) : IsSmooth (HMul.hMul r : X → X) := sorry
@[simp, diff]
theorem differential_of_hmul_1 : δ (HMul.hMul : ℝ → X → X) = λ (r dr : ℝ) (x : X) => dr * x := sorry
@[simp, diff]
theorem differential_of_hmul_2 (r : ℝ) : δ (HMul.hMul r : X → X) = λ (x dx : X) => r * dx := sorry

-- @[reducible]
-- instance : AtomicSmoothFun₂ (HAdd.hAdd : X → X → X) where
--   df₁ := λ x dx y => dx
--   df₂ := λ x y dy => dy
--   is_smooth₁ := sorry
--   is_smooth₂ := sorry
--   is_df₁ := sorry
--   is_df₂ := sorry

instance : IsSmooth (HAdd.hAdd : X → X → X) := sorry
instance (x : X) : IsSmooth (HAdd.hAdd x : X → X) := sorry
@[simp, diff]
theorem differential_of_add_1 : δ (HAdd.hAdd : X → X → X) = λ (x dx : X) (y : X) => dx := sorry
@[simp, diff]
theorem differential_of_add_2 (x : X) : δ (HAdd.hAdd x : X → X) = λ (y dy : X) => dy := sorry

-- @[reducible]
-- instance : AtomicSmoothFun₂ (HSub.hSub : X → X → X) where
--   df₁ := λ x dx y => dx
--   df₂ := λ x y dy => - dy
--   is_smooth₁ := sorry
--   is_smooth₂ := sorry
--   is_df₁ := sorry
--   is_df₂ := sorry

instance : IsSmooth (HSub.hSub : X → X → X) := sorry
instance (x : X) : IsSmooth (HSub.hSub x : X → X) := sorry
@[simp, diff]
theorem differential_of_sub_1 : δ (HSub.hSub : X → X → X) = λ (x dx : X) (y : X) => dx := sorry
@[simp, diff]
theorem differential_of_sub_2 (x : X) : δ (HSub.hSub x : X → X) = λ (y dy : X) => -dy := sorry

-- @[reducible]
-- instance {X} [SemiHilbert X] : AtomicSmoothFun₂ (λ (x y : X) Ω => ⟪x, y⟫[Ω]) where
--   df₁ := λ x dx y Ω => ⟪dx, y⟫[Ω]
--   df₂ := λ x y dy Ω => ⟪x, dy⟫[Ω]
--   is_smooth₁ := sorry
--   is_smooth₂ := sorry
--   is_df₁ := sorry
--   is_df₂ := sorry

instance {X} [SemiHilbert X] : IsSmooth (λ (x y : X) Ω => ⟪x, y⟫[Ω]) := sorry
instance {X} [SemiHilbert X] (x) : IsSmooth (λ (y : X) Ω => ⟪x, y⟫[Ω]) := sorry
@[simp, diff]
theorem differential_of_inner_1 {X} [SemiHilbert X] : δ  (λ (x y : X) Ω => ⟪x, y⟫[Ω]) = λ x dx y Ω => ⟪dx, y⟫[Ω] := sorry
@[simp, diff]
theorem differential_of_inner_2 {X} [SemiHilbert X] (x : X) : δ  (λ (y : X) Ω => ⟪x, y⟫[Ω]) = λ y dy Ω => ⟪x, dy⟫[Ω] := sorry

-- set_option trace.Meta.Tactic.simp.rewrite true in
-- @[reducible]
-- instance {X} [Hilbert X] : AtomicSmoothFun (λ x : X => ∥x∥²) where
--   df := λ x dx => 2 * ⟪x, dx⟫
--   is_smooth := by simp[SemiInner.normSqr] infer_instance done
--   is_df := by simp [SemiInner.normSqr] simp_rw [SemiHilbert.semi_inner_sym] simp done

instance {X} [Hilbert X] : IsSmooth (λ x : X => ∥x∥²) := sorry
@[simp, diff]
theorem differential_of_srqnorm {X} [Hilbert X] : δ (λ x : X => ∥x∥²) = λ x dx => 2 * ⟪x,dx⟫ := sorry

-- @[reducible]
-- instance {ι} [Enumtype ι] : AtomicSmoothFun (sum : (ι → X) → X) where
--   df := λ f df => sum df
--   is_smooth := sorry
--   is_df := sorry

instance {ι} [Enumtype ι] : IsSmooth (sum : (ι → X) → X) := sorry
@[simp, diff]
theorem differential_of_sum {ι} [Enumtype ι] : δ (sum : (ι → X) → X) = λ f df => sum df := sorry
