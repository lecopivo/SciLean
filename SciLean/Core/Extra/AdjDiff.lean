import SciLean.Core.Functions

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] 
variable {Y₁ Y₂ : Type} [SemiHilbert Y₁] [SemiHilbert Y₂]
variable {ι κ : Type} [Enumtype ι] [Enumtype κ] [Nonempty ι] [Nonempty κ]


@[simp]
theorem comp.arg_x_i.adjDiff_simp 
  (f : Y → Z) [HasAdjDiff f]
  (g : X → ι → Y) [HasAdjDiff g]
  : 
    δ† (λ x i => f (g x i)) = λ x dx' => (δ† g x) λ i => ((δ† f) (g x i) (dx' i))
:= by 
  funext x dx';
  simp [sum_of_linear, sum_into_lambda]
  done


@[simp high]
theorem diag.arg_x_i.adjDiff_simp 
  (f : Y₁ → Y₂ → Z) [IsSmooth f]
  [∀ y₂, HasAdjDiff λ y₁ => f y₁ y₂]
  [∀ y₁, HasAdjDiff λ y₂ => f y₁ y₂]
  (g₁ : X → ι → Y₁) [HasAdjDiff g₁]
  (g₂ : X → ι → Y₂) [HasAdjDiff g₂]
  : δ† (λ x i => f (g₁ x i) (g₂ x i))
    = 
    λ x dx' => 
      (δ† g₁ x) (λ i => (δ† (λ y₁ => f y₁ (g₂ x i))) (g₁ x i) (dx' i))
      +
      (δ† g₂ x) (λ i => (δ† (λ y₂ => f (g₁ x i) y₂)) (g₂ x i) (dx' i))
:= by 
  funext x dx';
  simp [sum_of_linear, sum_into_lambda, sum_of_add]
  done


@[simp low-1]
theorem eval.arg_x_i.adjDiff_simp {ι κ : Type} [Enumtype ι] [Enumtype κ] {X Z} [SemiHilbert X][ SemiHilbert Z]
  (g : ι → κ) [IsInv g] [Nonempty ι]
  (f : X → κ → Z) [HasAdjDiff f]
  : δ† (λ x i => f x (g i)) = (λ x dx' => (δ† f x) λ j => dx' (g⁻¹ j))
:= 
by
  simp [sum_of_linear, sum_into_lambda]
  done
