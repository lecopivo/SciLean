import SciLean
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

-- set_option trace.Meta.synthInstance true in
example {n} (y : Fin n → ℝ) : HasAdjointT fun (x : Fin n → ℝ) => ∑ i, x i * y i := by infer_instance
example {n m} (A : Fin n → Fin m → ℝ) (i : Fin n) : HasAdjointT fun (x : Fin m → ℝ) => ∑ j, A i j * x j := by infer_instance


example {n} :
  (λ (x : Fin n → ℝ) => ∑ i, (x i))†
  =
  (λ y i => y) := by simp only [comp.arg_x.adj_simp]; symdiff; done
#check swap.arg_y.adj_simp
set_option trace.Meta.Tactic.simp.rewrite true in
@[diff]
theorem adjoint_pointwise_fun (f : ι → X → Y) [∀ i, HasAdjointT (f i)]
  : (λ (x : ι → X) i => (f i) (x i))†
    =
    (λ (y : ι → Y) i => (f i)† (y i)) := by symdiff; sorry_proof 

set_option trace.Meta.Tactic.simp.rewrite true in
@[diff]
theorem adjoint_pointwise_array [PowType Xι ι X] (f : ι → X → Y) [∀ i, HasAdjointT (f i)]
  : (λ (x : X^ι)  => λ i => (f i) (x[i]))†
    =
    (λ (y : ι→Y) => ⊞ i,   (f i)† (y i)) := by symdiff; done

@[diff]
theorem adjoint_pointwise_smooth_fun {W X Y} [Hilbert X] [Hilbert Y] [Enumtype ι] [FinVec W ι] (f : W → X → Y) [∀ w, HasAdjointT (f w)] [IsSmoothNT 2 f]
  : (λ (x : W⟿X) => λ w ⟿ (f w) (x w))†
    =
    (λ (y : W⟿Y) => λ w ⟿ (f w)† (y w)) := by symdiff; sorry_proof

function_properties LinMap.val {X Y ι} [Enumtype ι] [FinVec X ι] [Hilbert Y] (f : X ⊸ Y) (x : X) : Y
argument f
  hasAdjoint := sorry_proof
  -- abbrev † := ⟨λ x' => ⟪x,x'⟫ * f',sorry_proof⟩ by sorry_proof -- TODO: is this really correct??? maybe raise or lower i
  -- ndex or `x`

instance LinMap.mk'.arg_f.composition.hasAdjoint {X Y ι} [Enumtype ι] [FinVec X ι] [Hilbert Y] 
  (f : W → X → Y) [hf : ∀ w, HasAdjointT (f w)] [∀ w, IsLinT (f w)]
  : have : IsLinT (f w) := ⟨(hf w).1.2⟩;
    HasAdjointT (λ w => λ x ⊸ f w x) := sorry_proof

@[diff]
theorem LinMap.mk'.arg_f.composition.adjoint_simp {X Y ι} [Enumtype ι] [FinVec X ι] [Hilbert Y] 
  (f : W → X → Y) [∀ w, HasAdjointT (f w)] [IsLinT f]
  : (λ w => λ x ⊸ f w x)†
    =
    λ g => sorry := sorry_proof


set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.simp.unify true in
@[diff]
theorem adjoint_pointwise_lin_fun {W X Y} [Hilbert X] [Hilbert Y] [Enumtype ι] [FinVec W ι] (f : X → Y) [hf : HasAdjointT f]
  : have : IsLinT f := ⟨hf.1.2⟩;
    (λ (x : W⊸X) => λ w ⊸ f (x w))†
    =
    (λ (y : W⊸Y) => λ w ⊸ f† (y w)) := by symdiff; sorry_proof

@[diff]
theorem adjoint_pointwise_fun_array [Enumtype I] [PowType YI I Y] (f : X → Y) [HasAdjointT f]
  : (λ (x : I → X) => ⊞ i, f (x i))†
    =
    (λ y i => f† y[i]) := by symdiff; done


@[diff]
theorem adjoint_pointwise_array_array [Enumtype I] [PowType XI I X] [PowType YI I Y] (f : X → Y) [HasAdjointT f]
  : (λ (x : X^I) => ⊞ i, f (x[i]))†
    =
    (λ y => ⊞ i, f† y[i]) := by symdiff; done



-- set_option trace.Meta.Tactic.simp.rewrite true in
-- set_option trace.Meta.Tactic.simp.unify true in
example {n} :
  (λ (x : Fin n → ℝ) i => 2*(x i))†
  =
  (λ y i => 2 * y i) := by symdiff; done

unif_hint (f? : X → Y)
  (op : X → X → Y)
where
  f? =?= λ x => op x x
  |-
  (λ (x : ι → X) i => f? (x i))†
  =?=
  (λ (x : ι → X) i => op (x i) (x i))†


example : HasAdjointT (λ x : X => x + x) := by infer_instance

example {n} :
  (λ (x : Fin n → ℝ) i => x i + x i)†
  =
  (λ y i => y i + y i) := 
by symdiff_core only []; done


example {n m : Nat} (f : Fin n → Fin m → ℝ → ℝ) [∀ i j, HasAdjointT (f i j)]
  : (λ (x : ℝ^{m}) => ⊞ i, ∑ j, (f i j) x[j])†
    =
    λ y => ⊞ j, ∑ i, (f i j)† y[i] :=
by
  unfold introPowElem
  symdiff; done


--------------------------------------------------------------------------------
-- Linear Algebra
--------------------------------------------------------------------------------




--------------------------------------------------------------------------------
-- Variants on transposing matrix multiplication and other tensor contractions
--------------------------------------------------------------------------------

example {n m} (A : Fin n → Fin m → ℝ) : 
  (λ (x : Fin m → ℝ) => λ i => ∑ j, A i j * x j)†
  =
  (λ y => λ i => ∑ j, A j i * y j) := by symdiff; done

example {n m} (A : ℝ^{n,m}) : 
  (λ (x : ℝ^{m}) => ⊞ i, ∑ j, A[i,j] * x[j])†
  =
  (λ y => ⊞ i, ∑ j, A[j,i] * y[j]) := by symdiff; done

example {n m} (A : Fin n → Fin m → ℝ) : 
  (λ (x : Fin m → ℝ) => λ i => ∑ j, x j * A i j)†
  =
  (λ y => λ i => ∑ j, y j * A j i) := by symdiff; done

example {n m} (A : Fin n → Fin m → ℝ) : 
  (λ (x : Fin m → ℝ) => λ i => ∑ j, 2 * x j * A i j)†
  =
  (λ y => λ i => ∑ j, 2 * y j * A j i) := by symdiff; done

example {n m} (A : Fin n → Fin m → ℝ) : 
  (λ (x : Fin m → ℝ) => λ i => ∑ j, A i j * x j * A i j)†
  =
  (λ y => λ i => ∑ j, A j i * y j * A j i) := by symdiff; done


-- Make these work!
example {n m} (A B : Fin n → Fin m → ℝ) : 
  (λ (x : Fin m → ℝ) => λ i => ∑ j, (A i j * x j + B i j * x j))†
  =
  (λ y => λ i => ∑ j, A j i * y j) := by symdiff; admit

example {n m l} (A : Fin n → Fin m → Fin l → ℝ) : 
  (λ (x : Fin m → Fin l → ℝ) => λ i => ∑ j k, A i j k * x j k)†
  =
  (λ y => λ j k => ∑ i, A i j k * y i) := 
by symdiff; admit


