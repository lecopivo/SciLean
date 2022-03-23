import SciLean.Operators.Calculus.Basic
import SciLean.Operators.Calculus.AtomicSmoothFun

namespace SciLean.Smooth

variable {α β γ : Type}
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]

----------------------------------------------------------------------

@[simp]
theorem diff_of_id
  : δ (λ x : X => x) = λ x dx => dx := sorry

@[simp low]
theorem diff_of_swap (f : α → X → Y) [∀ i, IsSmooth (f i)]
  : δ (λ (x : X) a => f a x) = λ x dx a => δ (f a) x dx := sorry

@[simp]
theorem diff_of_const 
  : δ (λ (x : X) (a : α) => x) = λ x dx a => dx := by simp done

@[simp low]
theorem diff_of_comp
  (f : Y → Z) [IsSmooth f] 
  (g : X → Y) [IsSmooth g] 
  : δ (λ x => f (g x)) = λ x dx => δ f (g x) (δ g x dx) := sorry

@[simp low]
theorem diff_of_diag
  (f : Y₁ → Y₂ → Z) [IsSmooth f] [∀ y₁, IsSmooth (f y₁)]
  (g₁ : X → Y₁) [IsSmooth g₁]
  (g₂ : X → Y₂) [IsSmooth g₂]
  : δ (λ x => f (g₁ x) (g₂ x)) 
    = 
    λ x dx => δ f (g₁ x) (δ g₁ x dx) (g₂ x) + 
              δ (f (g₁ x)) (g₂ x) (δ g₂ x dx) := sorry

@[simp low]
theorem diff_of_parm
  (f : X → α → Y) [IsSmooth f]
  (a : α)
  : δ (λ x => f x a) = λ x dx => δ f x dx a := sorry


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
  df₂ := λ r x dx => r * x
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

@[reducible]
instance {X} [Hilbert X] : AtomicSmoothFun (λ x : X => ∥x∥²) where
  df := λ x dx => 2 * ⟪x, dx⟫
  is_smooth := by simp[SemiInner.normSqr] infer_instance done
  is_df := by simp[SemiInner.normSqr, SemiHilbert.semi_inner_sym] done

@[reducible]
instance : AtomicSmoothFun (λ x : ℝ => Math.exp x) where
  df := λ x dx => dx * Math.exp x
  is_smooth := sorry
  is_df := sorry

@[reducible]
instance : AtomicSmoothFun (λ x : ℝ => Math.sin x) where
  df := λ x dx => dx * Math.cos x
  is_smooth := sorry
  is_df := sorry

@[reducible]
instance : AtomicSmoothFun (λ x : ℝ => Math.cos x) where
  df := λ x dx => - dx * Math.sin x
  is_smooth := sorry
  is_df := sorry

example {X} [Hilbert X] : δ (λ x : X => ⟪x, x⟫) = λ x dx => ⟪dx, x⟫ + ⟪x, dx⟫ := 
  by simp[AtomicSmoothFun₂.df₁, AtomicSmoothFun₂.df₂]
----------------------------------------------------------------------

example (a : α) (f : Y → α → Z) [IsSmooth f] (g : X → Y) [IsSmooth g]
  : δ (λ x => f (g x) a) = λ x dx => δ f (g x) (δ g x dx) a := by simp

example (f : Y → Z) [IsSmooth f]
  : δ (λ (g : α → Y) (a : α) => f (g a)) = λ g dg a => δ f (g a) (dg a) := by simp

example
  : δ (λ (f : β → Z) (g : α → β) (a : α) => f (g a)) = λ f df (g : α → β) a => df (g a) := by simp

example (f : Y → β → Z) (g : X → Y) [IsSmooth f] [IsSmooth g] (b) 
  : δ (λ x => f (g x) b) = λ x dx => δ f (g x) (δ g x dx) b := by simp

example (f : Y → β → Z) [IsSmooth f] (b)
  : δ (λ (g : α → Y) a => f (g a) b) = λ g dg a => δ f (g a) (dg a) b := by simp

example (f : β → Y → Z) (g : β → X → Y) [∀ b, IsSmooth (f b)] [∀ b, IsSmooth (g b)]
  : δ (λ x b => f b (g b x)) = λ x dx b => δ (f b) (g b x) (δ (g b) x dx) := by simp

example (f : Y → β → Z) (g : X → Y) [IsSmooth f] [IsSmooth g]
  : δ (λ x b => f (g x) b) = λ x dx b => δ f (g x) (δ g x dx) b := by simp

example (f : Y → β → Z) [IsSmooth f]
  : δ (λ (g : α → Y) a b => f (g a) b) = λ g dg a b => δ f (g a) (dg a) b := by simp

example (f : Y₁ → β2 → Z) (g2 : α → β2) [IsSmooth f] (g dg)
  : δ (λ  (g1 : α → Y₁) a => f (g1 a) (g2 a)) g dg = λ a => δ f (g a) (dg a) (g2 a) := by simp

example (f : β1 → Y₂ → Z) (g1 : α → β1) [∀ y1, IsSmooth (f y1)] 
  : δ (λ (g2 : α → Y₂) a => f (g1 a) (g2 a)) = λ g dg a => δ (f (g1 a)) (g a) (dg a) := by simp

example (f : Y₁ → Y₂ → β → Z) (g1 : X → Y₁) (g2 : X → Y₂)
  [IsSmooth f] [∀ y1, IsSmooth (f y1)] [IsSmooth g1] [IsSmooth g2]
  : δ (λ (x : X) (b : β) => f (g1 x) (g2 x) b) = λ x dx b => δ f (g1 x) (δ g1 x dx) (g2 x) b + δ (f (g1 x)) (g2 x) (δ g2 x dx) b := by simp
