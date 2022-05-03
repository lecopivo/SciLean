import SciLean.NewStyle.Adjoint
import SciLean.NewStyle.Diff

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
variable {Y₁ Y₂ : Type} [SemiHilbert Y₁] [SemiHilbert Y₂]
variable {ι : Type} [Enumtype ι]

instance id.arg_x.hasAdjDiff (x : X)
  : HasAdjoint $ δ (λ x' => x') x := by simp infer_instance

instance const.arg_x.hasAdjDiff (x : X)
  : HasAdjoint $ δ (λ (x' : X) (i : ι) => x') x := by simp infer_instance

instance const.arg_y.hasAdjDiff (x : X) (y : Y)
  : HasAdjoint $ δ (λ (y' : Y) => x) y := by simp infer_instance

instance (priority := low) swap.arg_y.hasAdjDiff
  (f : ι → Y → Z) [∀ x, IsSmooth (f x)] [∀ x y, HasAdjoint $ δ (f x) y]
  (y : Y)
  : HasAdjoint $ δ (λ y' x => f x y') y := by simp infer_instance

instance comp.arg_x.hasAdjDiff
  (f : Y → Z) [IsSmooth f] [∀ y, HasAdjoint (δ f y)]
  (g : X → Y) [IsSmooth g] [∀ x, HasAdjoint (δ g x)]
  (x : X)
  : HasAdjoint (δ (λ x' => f (g x')) x) := by simp infer_instance

instance diag.arg_x.hasAdjDiff
  (f : Y₁ → Y₂ → Z) [IsSmooth f] [∀ y₁, IsSmooth (f y₁)] 
  [∀ y₁ y₂, HasAdjoint (λ dy₁ => δ f y₁ dy₁ y₂)]
  [∀ y₁ y₂, HasAdjoint (λ dy₂ => δ (f y₁) y₂ dy₂)]
  (g₁ : X → Y₁) [IsSmooth g₁] [∀ x, HasAdjoint (δ g₁ x)]
  (g₂ : X → Y₂) [IsSmooth g₂] [∀ x, HasAdjoint (δ g₂ x)]
  (x : X)
  : HasAdjoint $ δ (λ x' => f (g₁ x') (g₂ x')) x := 
  by 
    simp
    have inst : HasAdjoint (λ yy : Z × Z => yy.1 + yy.2) := sorry
    infer_instance
