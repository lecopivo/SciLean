import SciLean.Core.Adjoint
import SciLean.Core.Diff

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
variable {Y₁ Y₂ : Type} [SemiHilbert Y₁] [SemiHilbert Y₂]
variable {ι : Type} [Enumtype ι]


class HasAdjDiff (f : X → Y) : Prop where
  isSmooth : IsSmooth f
  hasAdjDiff : ∀ x, HasAdjoint $ δ f x

theorem infer_HasAdjDiff {f : X → Y} [IsSmooth f] : (∀ x, HasAdjoint $ δ f x) → HasAdjDiff f := sorry

----------------------------------------------------------------------

instance id.arg_x.hasAdjDiff
  : HasAdjDiff (λ x : X => x) := by apply infer_HasAdjDiff; intro; simp; infer_instance

instance const.arg_x.hasAdjDiff
  : HasAdjDiff (λ (x : X) (i : ι) => x) := by apply infer_HasAdjDiff; intro; simp; infer_instance

instance const.arg_y.hasAdjDiff (x : X)
  : HasAdjDiff (λ (y : Y) => x) := by apply infer_HasAdjDiff; intro; simp; infer_instance

instance (priority := low) swap.arg_y.hasAdjDiff
  (f : ι → Y → Z) [inst : ∀ x, HasAdjDiff (f x)]
  : HasAdjDiff (λ y x => f x y) := 
by
  have is := λ x => (inst x).isSmooth
  have ia := λ x => (inst x).hasAdjDiff
  apply infer_HasAdjDiff; intro; simp; infer_instance


instance comp.arg_x.hasAdjDiff
  (f : Y → Z) [instf : HasAdjDiff f] 
  (g : X → Y) [instg : HasAdjDiff g]
  : HasAdjDiff (λ x => f (g x)) := 
by 
  have isf := instf.isSmooth
  have iaf := instf.hasAdjDiff
  have isg := instg.isSmooth
  have iag := instg.hasAdjDiff

  apply infer_HasAdjDiff; intro; simp; infer_instance

instance diag.arg_x.hasAdjDiff
  (f : Y₁ → Y₂ → Z) [IsSmooth f] -- Smoothness in y₁ and y₂ does not guarantee joint smoothness
  [instf1 : ∀ y₂, HasAdjDiff λ y₁ => f y₁ y₂] 
  [instf2 : ∀ y₁, HasAdjDiff λ y₂ => f y₁ y₂]
  (g₁ : X → Y₁) [instg1 : HasAdjDiff g₁] -- [IsSmooth g₁] [∀ x, HasAdjoint (δ g₁ x)]
  (g₂ : X → Y₂) [instg2 : HasAdjDiff g₂]-- [IsSmooth g₂] [∀ x, HasAdjoint (δ g₂ x)]
  : HasAdjDiff (λ x => f (g₁ x) (g₂ x)) := 
  by 
    have isg1 := instg1.isSmooth
    have iag1 := instg1.hasAdjDiff
    have isg2 := instg2.isSmooth
    have iag2 := instg2.hasAdjDiff
    have isf1 := λ y => (instf1 y).isSmooth
    have iaf1 := λ y => (instf1 y).hasAdjDiff
    have isf2 := λ y => (instf2 y).isSmooth
    have iaf2 := λ y => (instf2 y).hasAdjDiff

    have inst : HasAdjoint (λ yy : Z × Z => yy.1 + yy.2) := sorry

    simp at iaf1
    
    apply infer_HasAdjDiff; intro; simp; infer_instance

instance eval.arg_x.parm1.hasAdjDiff
  (f : X → ι → Z) [inst : HasAdjDiff f] (i : ι)
  : HasAdjDiff (λ x => f x i) := 
  by
    have isf := inst.isSmooth
    have iaf := inst.hasAdjDiff

    apply infer_HasAdjDiff; intro; simp; infer_instance

----------------------------------------------------------------------

instance comp.arg_x.parm1.hasAdjDiff
  (a : α)
  (f : Y → α → Z) [HasAdjDiff λ y => f y a]
  (g : X → Y) [HasAdjDiff g]
  : HasAdjDiff λ x => f (g x) a := 
  by 
    apply comp.arg_x.hasAdjDiff (λ y => f y a) g
    done

instance diag.arg_x.parm1.hasAdjDiff
  (a : α)
  (f : Y₁ → Y₂ → α → Z) [IsSmooth λ y₁ y₂ => f y₁ y₂ a]
  [instf1 : ∀ y₂, HasAdjDiff λ y₁ => f y₁ y₂ a] 
  [instf2 : ∀ y₁, HasAdjDiff λ y₂ => f y₁ y₂ a]
  (g₁ : X → Y₁) [HasAdjDiff g₁] 
  (g₂ : X → Y₂) [HasAdjDiff g₂]
  : HasAdjDiff λ x => f (g₁ x) (g₂ x) a := 
  by 
    apply diag.arg_x.hasAdjDiff (λ y₁ y₂ => f y₁ y₂ a) g₁ g₂
    done


