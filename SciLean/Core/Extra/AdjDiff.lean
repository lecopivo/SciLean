import SciLean.Core.Functions

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] 
variable {Y₁ Y₂ : Type} [SemiHilbert Y₁] [SemiHilbert Y₂]
variable {ι κ : Type} [Enumtype ι] [Enumtype κ] [Nonempty ι] [Nonempty κ]

@[simp ↓]
theorem swap.arg_f.adjDiff_simp 
  : δ† (λ (f : ι → κ → X) (j : κ) (i : ι) => f i j) = λ f df' i j => df' j i
:= by 
  funext x dx';
  simp [sum_of_linear, sum_into_lambda]
  done

 -- δ†fun x i j => getOp x i

@[simp ↓]
theorem eval.arg_x_i.adjDiff_simp 
  (f : X → ι → Y) [HasAdjDiff f]
  : δ† (λ (x : X) (i : ι) (j : κ) => f x i) = λ x dx' => δ† f x (λ i => ∑ j, dx' i j)
:= by
  funext x dx'; simp;
  simp [sum_of_linear, sum_into_lambda]
  done

@[simp ↓]
theorem comp.arg_x_i.adjDiff_simp 
  (f : Y → Z) [HasAdjDiff f]
  (g : X → ι → Y) [HasAdjDiff g]
  : 
    δ† (λ x i => f (g x i)) = λ x dx' => (δ† g x) λ i => ((δ† f) (g x i) (dx' i))
:= by 
  funext x dx';
  simp [sum_of_linear, sum_into_lambda]
  done

@[simp ↓]
theorem comp.arg_x_i_j.adjDiff_simp 
  (f : Y → Z) [HasAdjDiff f]
  (g : X → ι → κ → Y) [HasAdjDiff g]
  : 
    δ† (λ x i j => f (g x i j)) = λ x dx' => (δ† g x) λ i j => ((δ† f) (g x i j) (dx' i j))
:= by 
  funext x dx';
  simp [sum_of_linear, sum_into_lambda]
  done



@[simp ↓]
theorem comp.arg_x_i.arg1.adjDiff_simp 
  (f : Y → ι → Z) [HasAdjDiff f]
  (g : X → ι → Y) [HasAdjDiff g]
  : 
    δ† (λ x i => f (g x i) i) = λ x dx' => (δ† g x) λ i => ((δ† f) (g x i) (λ j => kron i j * dx' i))
:= by 
  funext x dx';
  simp [sum_of_linear, sum_into_lambda]
  done

@[simp ↓]
theorem comp.arg_x_i.arg1'.adjDiff_simp 
  (f : ι → Y → Z) [∀ i, HasAdjDiff (f i)]
  (g : X → ι → Y) [HasAdjDiff g]
  : 
    δ† (λ x i => f i (g x i)) = λ x dx' => (δ† g x) λ i => ((δ† (f i)) (g x i) (dx' i))
:= by 
  funext x dx';
  simp [sum_of_linear, sum_into_lambda]
  done

-- set_option trace.Meta.Tactic.simp.rewrite true in
@[simp ↓ high]
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

@[simp ↓ low-3]
theorem scomb.arg_x_i_j.adjDiff_simp 
  {X Y Z : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] 
  {ι κ : Type} [Enumtype ι] [Enumtype κ] [Nonempty ι] [Nonempty κ]
  (f : X → ι → κ → Y →  Z) [IsSmooth f]
  [∀ y, HasAdjDiff λ x i j => f x i j y]
  [∀ x, HasAdjDiff λ y i j => f x i j y]
  (g : X → ι → κ → Y) [HasAdjDiff g]
  : δ† (λ x i j => f x i j (g x i j) )
    = 
    λ x dx' => 
      (δ† (hold λ x' i j => f x' i j (g x i j)) x dx')
      +
      (δ† g x) (λ i j => (δ† (λ y => f x i j y) (g x i j) (dx' i j)))
:= by 
   admit

-- @[simp ↓ low-2]
-- theorem scomb.arg_x_i_j.parm1.adjDiff_simp 
--   {X Y Z : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] 
--   {ι κ : Type} [Enumtype ι] [Enumtype κ] [Nonempty ι] [Nonempty κ]
--   {α₁ : Type} (a₁ : ι → κ → α₁)
--   (f : X → ι → κ → Y → α₁ → Z) [IsSmooth f]
--   [∀ y, HasAdjDiff λ x i j => f x i j y (a₁ i j)]
--   [∀ x, HasAdjDiff λ y i j => f x i j y (a₁ i j)]
--   (g : X → ι → κ → Y) [HasAdjDiff g]
--   : δ† (λ x i j => f x i j (g x i j) (a₁ i j))
--     = 
--     λ x dx' => 
--       (δ† (hold λ x' i j => f x' i j (g x i j) (a₁ i j)) x dx')
--       +
--       (δ† g x) (λ i j => (δ† (λ y => f x i j y (a₁ i j)) (g x i j) (dx' i j)))
-- := by 
--   admit

-- set_option trace.Meta.Tactic.simp.rewrite true in
@[simp ↓ high]
theorem diag.arg_x_i_j.adjDiff_simp 
  (f : Y₁ → Y₂ → Z) [IsSmooth f]
  [∀ y₂, HasAdjDiff λ y₁ => f y₁ y₂]
  [∀ y₁, HasAdjDiff λ y₂ => f y₁ y₂]
  (g₁ : X → ι → κ → Y₁) [hg₁ : HasAdjDiff g₁]
  (g₂ : X → ι → κ → Y₂) [hg₂ : HasAdjDiff g₂]
  : δ† (λ x i j => f (g₁ x i j) (g₂ x i j))
    = 
    λ x dx' => 
      (δ† g₁ x) (λ i j => (δ† (λ y₁ => f y₁ (g₂ x i j))) (g₁ x i j) (dx' i j))
      +
      (δ† g₂ x) (λ i j => (δ† (λ y₂ => f (g₁ x i j) y₂)) (g₂ x i j) (dx' i j))
:= by 
  have sg₁ := hg₁.1
  have sg₂ := hg₂.1
  simp; unfold hold; simp; unfold hold; simp
  admit


-- set_option trace.Meta.Tactic.simp.rewrite true in
example {n} [Fact (n≠0)] : (δ†fun (x : Fin n → ℝ) (i j : Fin n) => x j) = λ x dx' => ∑ i, dx' i := 
by
  simp



@[simp ↓ low-1]
theorem comp.arg_x_i.adjDiff_simp' {ι κ : Type} [Enumtype ι] [Enumtype κ] {X Z} [SemiHilbert X] [SemiHilbert Z]
  (g : ι → κ) [IsInv g] [Nonempty ι]
  (f : X → κ → Z) [HasAdjDiff f]
  : δ† (λ x i => f x (g i)) = (λ x dx' => (δ† f x) λ j => dx' (g⁻¹ j))
:= 
by 
  simp [sum_of_linear, sum_into_lambda]
  done
