import SciLean.Operators.Calculus.DiffCore
import SciLean.Operators.Adjoint

namespace SciLean

variable {X Y Z : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
variable {Y₁ Y₂ : Type} [SemiHilbert Y₁] [SemiHilbert Y₂]
variable {ι κ : Type} [Enumtype ι] [Enumtype κ]

-- class IsRevSmooth (f : X → Y) where
--   is_smooth : IsSmooth f := by infer_instance
--   df_has_adjoint (x) : HasAdjoint (δ f x)

----------------------------------------------------------------------

instance is_rev_smooth_id (x : X) 
  : HasAdjoint (δ (λ x : X => x) x) :=
by 
  simp infer_instance done

instance is_rev_smooth_const (x : X) (y : Y) 
  : HasAdjoint (δ (λ y : Y => x) y) :=
by
  simp infer_instance done

instance is_rev_smooth_swap (x)
  (f : ι → X → Y) [∀ i, IsSmooth (f i)] [∀ i x, HasAdjoint (δ (f i) x)]
  : HasAdjoint (δ (λ x i => f i x) x) :=
by
  simp infer_instance done

instance is_rev_smooth_parm (i x)
  (f : X → ι → Y) [IsSmooth f] [HasAdjoint (δ f x)] 
  : HasAdjoint (δ (λ x => f x i) x) :=
by
  simp infer_instance done

instance is_rev_smooth_comp (x)
  (f : Y → Z) [IsSmooth f] [∀ y, HasAdjoint (δ f y)] 
  (g : X → Y) [IsSmooth g] [∀ x, HasAdjoint (δ g x)] 
  : HasAdjoint (δ (λ x => f (g x)) x) :=
by
  simp infer_instance done

instance is_rev_smooth_diag (x)
  (f : Y₁ → Y₂ → Z) [IsSmooth f] [∀ y₁, IsSmooth (f y₁)] 
  [∀ y₁ y₂, HasAdjoint (λ dy₁ => δ f y₁ dy₁ y₂)]
  [∀ y₁ y₂, HasAdjoint (λ dy₂ => δ (f y₁) y₂ dy₂)]
  (g₁ : X → Y₁) [IsSmooth g₁] [∀ x, HasAdjoint (δ g₁ x)]
  (g₂ : X → Y₂) [IsSmooth g₂] [∀ x, HasAdjoint (δ g₂ x)]
  : HasAdjoint (δ (λ x => f (g₁ x) (g₂ x)) x) :=
by
  simp infer_instance done
