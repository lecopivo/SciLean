import SciLean.Core
-- import SciLean.Tactic.AutoDiff

open SciLean

variable {α β γ : Type}
variable {X Y Z W : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] [SemiHilbert W]
variable {Y₁ Y₂ : Type} [SemiHilbert Y₁] [SemiHilbert Y₂]
variable {ι κ : Type} [Enumtype ι] [Enumtype κ]

-- set_option maxHeartbeats 4000
-- set_option synthInstance.maxHeartbeats 1000
-- set_option synthInstance.maxSize 80

#check sum

example {n} (i : Fin n) : HasAdjointT fun (x : Fin n → ℝ) => x i := by infer_instance
example {n} : HasAdjointT fun (x : Fin n → ℝ) => sum x := by infer_instance
example {n} : HasAdjointT fun (x : Fin n → ℝ) => ∑ i, x i := by infer_instance
example {n} (y : Fin n → ℝ) : HasAdjointT fun (x : Fin n → ℝ) => ∑ i, y i * x i := by infer_instance

set_option trace.Meta.synthInstance true in
example {n} (y : Fin n → ℝ) : HasAdjointT fun (x : Fin n → ℝ) => ∑ i, x i * y i := by infer_instance
example {n m} (A : Fin n → Fin m → ℝ) (i : Fin n) : HasAdjointT fun (x : Fin m → ℝ) => ∑ j, A i j * x j := by infer_instance

--------------------------------------------------------------------------------
-- Linear Algebra
--------------------------------------------------------------------------------

-- set_option trace.Meta.Tactic.simp.discharge true in


example {n m} (A : Fin n → Fin m → ℝ) : 
  (λ (x : Fin m → ℝ) => λ i => ∑ j, A i j * x j)†
  =
  (λ y => ∑ j i', λ i => [[i'=i]] * A j i' * y j) := by symdiff; done



example (x : Fin n → ℝ) 
  : (λ (w : Fin 3 → ℝ) => λ i : Fin n => ∑ j : Fin 3, w j * x ⟨i.1 + j.1, sorry_proof⟩)†
    =
    λ x' => λ j => sorry := by symdiff; sorry_proof



-- @[diff]
-- theorem eval_sum_duality 
--   (f : ι → κ → X → Y) [∀ i j, HasAdjointT (f i j)]
--   : (λ (x : ι → X) => λ j => ∑ i, (f i j) (x i))†
--     =
--     λ y => λ i => ∑ j, (f i j)† (y j)
--   := by symdiff; sorry_proof


@[diff]
theorem adjoint_sum_eval
  (f : ι → κ → X → Y) [∀ i j, HasAdjointT (f i j)]
  : (λ (x : κ → X) => λ i => ∑ j, (f i j) (x j))†
    =
    λ y => λ j => ∑ i, (f i j)† (y i)
  := by symdiff; sorry_proof


-- @[diff]
theorem eval_sum_duality' 
  (f : ι → κ → X → α → Z) [∀ i j a, HasAdjointT (λ x => f i j x a)]
  (g : ι → κ → α)
  : (λ (x : κ → X) => λ i => ∑ j, f i j (x j) (g i j))†
    =
    λ y => λ j => ∑ i, (λ x => f i j x (g i j))† (y i)
  := by apply adjoint_sum_eval (λ i j x => f i j x (g i j)); done


unif_hint 
  (f? : ι → κ → X → Y) 
  (f : ι → κ → X → α → Y) (g : ι → κ → α)
where
  f? =?= λ i j x => f i j x (g i j)
  |-
  (λ (x : κ → X) => λ i => ∑ j, (f? i j) (x j))† 
  =?= 
  (λ (x : κ → X) => λ i => ∑ j, f i j (x j) (g i j))†


unif_hint 
  (f? : ι → κ → X → Y) 
  (f : ι → κ → W → α → Y) (g : ι → κ → α) (h : ι → κ → X → W)
where
  f? =?= λ i j x => f i j (h i j x) (g i j)
  |-
  (λ (x : κ → X) => λ i => ∑ j, (f? i j) (x j))† 
  =?= 
  (λ (x : κ → X) => λ i => ∑ j, f i j (h i j (x j)) (g i j))†


unif_hint 
  (f? : ι → κ → X → Y) 
  (f : ι → κ → W → Z → α → Y) (g : ι → κ → α) (h : ι → κ → X → W) (h' : ι → κ → X → Z)
where
  f? =?= λ i j x => f i j (h i j x) (h' i j x) (g i j)
  |-
  (λ (x : κ → X) => λ i => ∑ j, (f? i j) (x j))† 
  =?= 
  (λ (x : κ → X) => λ i => ∑ j, f i j (h i j (x j)) (h' i j (x j)) (g i j))†



-- @[diff]
-- theorem comp.arg_x_i.adjDiff_sim'''
--   (f : Y → κ → Z) 
--   (g : (ι → X) → Y) 
--   : 
--     (λ x j => f (g x) j)† 
--     = 
--     λ x' =>   
--     let y' := f† x'
--     let z' := g† y'
--     z'
-- := by 
--   funext y; simp
--   symdiff; admit


-- @[diff]
-- theorem comp.arg_x_i.adjDiff_simp 
--   (f : Y → Z) 
--   (g : X → ι → Y) 
--   : 
--     (λ x i => f (g x i))† 
--     = 
--     λ x' =>   
--     let y' := λ i => f† (x' i)
--     let z' := g† y'
--     z'
-- := by 
--   funext y; simp
--   symdiff; admit


-- @[diff]
-- theorem hah2 (f : ι → κ → X → X) : (λ x : ι → X => λ j => ∑ i, f i j (x i))†
--                 = 
--                 λ y => λ i => ∑ j, (f i j)† (y j) := sorry_proof


set_option trace.Meta.Tactic.simp.rewrite true in
example {n m} (A : Fin n → Fin m → ℝ) : 
  (λ (x : Fin m → ℝ) => λ i => ∑ j, A i j * x j)†
  =
  (λ y => λ i => ∑ j, A j i * y j) := by symdiff; done


example {n m} (A : Fin n → Fin m → ℝ) : 
  (λ (x : Fin m → ℝ) => λ i => ∑ j, x j * A i j)†
  =
  (λ y => λ i => ∑ j, y j * A j i) :=
by
  symdiff; done


example {n m} (A : Fin n → Fin m → ℝ) : 
  (λ (x : Fin m → ℝ) => λ i => ∑ j, (2:ℝ) * x j * A i j)†
  =
  (λ y => λ i => ∑ j, (2:ℝ) * y j * A j i) :=
by
  symdiff; done



example {n m} (A : Fin n → Fin m → ℝ) : 
  (λ (x : Fin m → ℝ) => λ i => ∑ j, 2 * x j * A i j)†
  =
  (λ y => λ i => ∑ j, 2 * y j * A j i) := by symdiff; done


example {n m} (A : Fin n → Fin m → ℝ) : 
  (λ (x : Fin m → ℝ) => λ i => ∑ j, A i j * x j * A i j)†
  =
  (λ y => λ i => ∑ j, A j i * y j * A j i) := by symdiff; done


example {n m} (A B : Fin n → Fin m → ℝ) : 
  (λ (x : Fin m → ℝ) => λ i => ∑ j, (A i j * x j + B i j * x j))†
  =
  (λ y => λ i => ∑ j, A j i * y j) := by symdiff; done


set_option synthInstance.maxSize 2000 

set_option trace.Meta.Tactic.simp.rewrite true in
example {n m l} (A : Fin n → Fin m → Fin l → ℝ) : 
  (λ (x : Fin m → Fin l → ℝ) => λ i => ∑ j k, A i j k * x j k)†
  =
  (λ y => λ j k => ∑ i, A i j k * y i) := 
by
  rw [eval_sum_duality λ 
  symdiff; done



variable (g : X → X) (f : X → X) [IsSmoothT g] [IsSmoothT f]
 

#check 
  ∂ (λ x => 
     let y := g x
     let z := f y
     x + y + z) 
  rewrite_by 
  autodiff
