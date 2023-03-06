import SciLean.Core.AdjDiff


namespace SciLean



variable {α β γ : Type}
variable {X Y Z W : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] [SemiHilbert W]
variable {Y₁ Y₂ : Type} [SemiHilbert Y₁] [SemiHilbert Y₂]
variable {ι κ : Type} [Enumtype ι] [Enumtype κ]





@[diff]
theorem adjoint_sum_eval
  (f : ι → κ → X → Y) [∀ i j, HasAdjointT (f i j)]
  : (λ (x : κ → X) => λ i => ∑ j, (f i j) (x j))†
    =
    λ y => λ j => ∑ i, (f i j)† (y i)
  := by symdiff; sorry_proof

set_option trace.Meta.Tactic.simp.rewrite true in
@[diff]
theorem adjDiff_sum_eval
  (f : ι → κ → X → Y) [hf : ∀ i j, HasAdjDiffT (f i j)]
  : ∂† (λ (x : κ → X) => λ i => ∑ j, (f i j) (x j))
    =
    λ _ dy => λ j => ∑ i, ∂† (f i j) x (dy i)
  := by unfold adjointDifferential
        have  := λ i j => (hf i j).1.1
        symdiff; symdiff; sorry_proof

