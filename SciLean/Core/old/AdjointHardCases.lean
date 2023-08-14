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
  := by sorry -- symdiff; sorry_proof

@[diff]
theorem adjDiff_sum_eval
  (f : ι → κ → X → Y) [hf : ∀ i j, HasAdjDiffT (f i j)]
  : ∂† (λ (x : κ → X) => λ i => ∑ j, (f i j) (x j))
    =
    λ x dy => λ j => ∑ i, ∂† (f i j) (x j) (dy i) := 
by 
  unfold adjointDifferential
  have  := λ i j => (hf i j).1
  have  := λ i j => (hf i j).2
  sorry -- symdiff; symdiff
  -- done

@[diff]
theorem revDiff_sum_eval
  (f : ι → κ → X → Y) [hf : ∀ i j, HasAdjDiffT (f i j)]
  : ℛ (λ (x : κ → X) => λ i => ∑ j, (f i j) (x j))
    =
    λ x => (λ i => ∑ j, (f i j) (x j), 
            λ dy => λ j => ∑ i, ∂† (f i j) (x j) (dy i)) := 
by 
  unfold reverseDifferential; symdiff; done


unif_hint adjoint_sum_eval.unif_hint_1
  (f? : ι → κ → X → Y) 
  (f : ι → κ → X → α → Y) (g : ι → κ → α)
where
  f? =?= λ i j x => f i j x (g i j)
  |-
  (λ (x : κ → X) => λ i => ∑ j, (f? i j) (x j))† 
  =?= 
  (λ (x : κ → X) => λ i => ∑ j, f i j (x j) (g i j))†

unif_hint adjoint_sum_eval.unif_hint_2
  (f? : ι → κ → X → Y) 
  (f : ι → κ → W → α → Y) (g : ι → κ → α) (h : ι → κ → X → W)
where
  f? =?= λ i j x => f i j (h i j x) (g i j)
  |-
  (λ (x : κ → X) => λ i => ∑ j, (f? i j) (x j))† 
  =?= 
  (λ (x : κ → X) => λ i => ∑ j, f i j (h i j (x j)) (g i j))†


unif_hint adjoint_sum_eval.unif_hint_3
  (f? : ι → κ → X → Y) 
  (f : ι → κ → W → Z → α → Y) (g : ι → κ → α) (h : ι → κ → X → W) (h' : ι → κ → X → Z)
where
  f? =?= λ i j x => f i j (h i j x) (h' i j x) (g i j)
  |-
  (λ (x : κ → X) => λ i => ∑ j, (f? i j) (x j))†
  =?= 
  (λ (x : κ → X) => λ i => ∑ j, f i j (h i j (x j)) (h' i j (x j)) (g i j))†


unif_hint adjDiff_sum_eval.unif_hint_1
  (f? : ι → κ → X → Y) 
  (f : ι → κ → X → α → Y) (g : ι → κ → α)
where
  f? =?= λ i j x => f i j x (g i j)
  |-
  ∂† (λ (x : κ → X) => λ i => ∑ j, (f? i j) (x j)) 
  =?= 
  ∂† (λ (x : κ → X) => λ i => ∑ j, f i j (x j) (g i j))

unif_hint adjDiff_sum_eval.unif_hint_2
  (f? : ι → κ → X → Y) 
  (f : ι → κ → W → α → Y) (g : ι → κ → α) (h : ι → κ → X → W)
where
  f? =?= λ i j x => f i j (h i j x) (g i j)
  |-
  ∂† (λ (x : κ → X) => λ i => ∑ j, (f? i j) (x j))
  =?= 
  ∂† (λ (x : κ → X) => λ i => ∑ j, f i j (h i j (x j)) (g i j))

unif_hint adjDiff_sum_eval.unif_hint_3
  (f? : ι → κ → X → Y) 
  (f : ι → κ → W → Z → α → Y) (g : ι → κ → α) (h : ι → κ → X → W) (h' : ι → κ → X → Z)
where
  f? =?= λ i j x => f i j (h i j x) (h' i j x) (g i j)
  |-
  ∂† (λ (x : κ → X) => λ i => ∑ j, (f? i j) (x j))
  =?= 
  ∂† (λ (x : κ → X) => λ i => ∑ j, f i j (h i j (x j)) (h' i j (x j)) (g i j))

unif_hint revDiff_sum_eval.unif_hint_1
  (f? : ι → κ → X → Y) 
  (f : ι → κ → X → α → Y) (g : ι → κ → α)
where
  f? =?= λ i j x => f i j x (g i j)
  |-
  ℛ (λ (x : κ → X) => λ i => ∑ j, (f? i j) (x j)) 
  =?= 
  ℛ (λ (x : κ → X) => λ i => ∑ j, f i j (x j) (g i j))

unif_hint revDiff_sum_eval.unif_hint_2
  (f? : ι → κ → X → Y) 
  (f : ι → κ → W → α → Y) (g : ι → κ → α) (h : ι → κ → X → W)
where
  f? =?= λ i j x => f i j (h i j x) (g i j)
  |-
  ℛ (λ (x : κ → X) => λ i => ∑ j, (f? i j) (x j))
  =?= 
  ℛ (λ (x : κ → X) => λ i => ∑ j, f i j (h i j (x j)) (g i j))


unif_hint revDiff_sum_eval.unif_hint_3
  (f? : ι → κ → X → Y) 
  (f : ι → κ → W → Z → α → Y) (g : ι → κ → α) (h : ι → κ → X → W) (h' : ι → κ → X → Z)
where
  f? =?= λ i j x => f i j (h i j x) (h' i j x) (g i j)
  |-
  ℛ (λ (x : κ → X) => λ i => ∑ j, (f? i j) (x j))
  =?= 
  ℛ (λ (x : κ → X) => λ i => ∑ j, f i j (h i j (x j)) (h' i j (x j)) (g i j))


