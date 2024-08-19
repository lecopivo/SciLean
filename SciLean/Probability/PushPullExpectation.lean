import SciLean.Probability.Rand
-- import SciLean.Core.FunctionPropositions
-- import Mathlib

namespace SciLean.Rand

set_option deprecated.oldSectionVars true
variable
  {R} [RealScalar R]
  {X : Type _} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
  {Y : Type _} [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
  {Z : Type _} [AddCommGroup Z] [Module ℝ Z] [TopologicalSpace Z]

open Rand

set_option trace.Meta.Tactic.simp.discharge true
@[rand_pull_E]
theorem bind_pull_mean (x : Rand X) (f : X → Rand Y) :
    (x >>= (fun x' => pure (f x').mean)).mean
    =
    (x >>= f).mean := by simp[rand_push_E]

@[rand_push_E]
theorem ite_push_E {c} [Decidable c] (t e : Rand X) (φ : X → Y):
    (if c then t else e).𝔼 φ = (if c then t.𝔼 φ else e.𝔼 φ) := by
  if h : c then simp[h] else simp[h]

-- I don't think this is a desirable `rand_pull_E` theorem as it duplicates the if statement
-- @[rand_pull_E]
theorem ite_pull_E {c} [Decidable c] (t e : Rand X) (φ ψ : X → Y):
    (if c then t.𝔼 φ else e.𝔼 ψ) = (if c then t else e).𝔼 (if c then φ else ψ) := by
  if h : c then simp[h] else simp[h]

@[rand_push_E]
theorem ite_push_mean {c} [Decidable c] (t e : Rand X) :
    (if c then t else e).mean = (if c then t.mean else e.mean) := by
  if h : c then simp[h] else simp[h]

@[rand_pull_E]
theorem ite_pull_mean {c} [Decidable c] (t e : Rand X) :
    (if c then t.mean else e.mean) = (if c then t else e).mean := by
  if h : c then simp[h] else simp[h]

@[rand_pull_E mid-1]
theorem ite_pull_mean_t {c} [Decidable c] (t : Rand X) (e : X) :
    (if c then t.mean else e) = (if c then t else pure e).mean := by
  if h : c then simp[h] else simp[h]

@[rand_pull_E mid-1]
theorem ite_pull_mean_f {c} [Decidable c] (t : X) (e : Rand X) :
    (if c then t else e.mean) = (if c then pure t else e).mean := by
  if h : c then simp[h] else simp[h]

-- this has messed up universes
@[rand_pull_E]
theorem pull_E_lambda (r : Rand Y) (f : X → Y → Z) :
    (fun x => r.𝔼 (fun y => f x y))
    =
    r.𝔼 (fun y x => f x y) := sorry_proof

-- this has messed up universes
@[rand_push_E]
theorem push_E_lambda (r : Rand Y) (f : X → Y → Z) :
    r.𝔼 (fun y x => f x y)
    =
    (fun x => r.𝔼 (fun y => f x y)) := sorry_proof

-- can't be simp as it has variable head
set_option linter.unusedVariables false in
theorem pull_E_affine (r : Rand X) (φ : X → Y)
    (f : Y → Z) (hf : IsAffineMap ℝ f := by fun_prop) :
    (f (r.𝔼 φ)) = r.𝔼 (fun x => f (φ x)) := by sorry_proof -- have := hf; sorry_proof

@[rand_push_E]
theorem push_E_affine (r : Rand X) (φ : X → Y)
    (f : Y → Z) (hf : IsAffineMap ℝ f := by fun_prop) :
    r.𝔼 (fun x => f (φ x)) = (f (r.𝔼 φ)) := by rw[pull_E_affine (hf:=hf)]

@[rand_pull_E]
theorem pull_mean_add (x y : Rand X) :
    x.mean + y.mean
    =
    Rand.mean do
      let x' ← x
      let y' ← y
      return x' + y' := sorry_proof

@[rand_pull_E]
theorem pull_mean_add_1 (x : Rand X) (y : X) :
    x.mean + y
    =
    Rand.mean do
      let x' ← x
      return x' + y := sorry_proof

@[rand_pull_E]
theorem pull_mean_add_2 (x : X) (y : Rand X) :
    x + y.mean
    =
    Rand.mean do
      let y' ← y
      return x + y' := sorry_proof

@[rand_pull_E]
theorem pull_mean_sub (x y : Rand X) :
    x.mean - y.mean
    =
    Rand.mean do
      let x' ← x
      let y' ← y
      return x' - y' := sorry_proof

@[rand_pull_E]
theorem pull_mean_smul [Module R X] (r : R) (x : Rand X) :
    r • x.mean
    =
    Rand.mean do
      let x' ← x
      return r • x' := sorry_proof

@[rand_pull_E]
theorem pull_mean_mul (r : R) (x : Rand R) :
    r * x.mean
    =
    Rand.mean do
      let x' ← x
      return r * x' := sorry_proof

@[rand_pull_E]
theorem pull_mean_div (x : Rand R) (y : R) :
    x.mean / y
    =
    Rand.mean do
      let x' ← x
      return x' / y:= sorry_proof


@[rand_pull_E]
theorem pull_mean_neg (x : Rand X) :
    - x.mean
    =
    Rand.mean do
      let x' ← x
      return - x' := sorry_proof


section Nat

variable
  (C : ℕ → Type) [∀ n, AddCommGroup (C n)] [∀ n, Module ℝ (C n)] [∀ n, TopologicalSpace (C n)]
  [∀ n, MeasurableSpace (C n)] [∀ n, MeasurableSingletonClass (C n)]
  (D : ℕ → Type) [∀ n, MeasurableSpace (D n)] [∀ n, MeasurableSpace (D n)]


@[rand_pull_E]
theorem pull_E_nat_rec (x₀ : C 0) (r : (n : Nat) → Rand (D n))
    (f : (n : ℕ) → C n → D n → (C (n+1))) (hf : ∀ n d, IsAffineMap ℝ (f n · d)) :
    Nat.rec
      x₀
      (fun n x => (r n).𝔼 (f n x)) n
    =
    (Nat.rec (motive:=fun n => Rand (C n))
      (pure x₀)
      (fun n x => do
        let x' ← x
        let y' ← r n
        pure (f n x' y')) n).mean := by
  induction n
  case zero => simp[mean]
  case succ n hn =>
    simp[hn,mean,map]
    conv => simp[rand_pull_E,map]
    conv =>
      lhs
      enter[1,2,x',1]
      unfold mean
      simp[pull_E_affine (f:=(f n · x'))]
    conv =>
      simp[rand_pull_E]
    rw[Rand.swap_bind]


@[rand_pull_E]
theorem pull_E_nat_recOn (x₀ : C 0) (r : (n : Nat) → Rand (D n))
    (f : (n : ℕ) → C n → D n → (C (n+1))) (hf : ∀ n d, IsAffineMap ℝ (f n · d)) :
    Nat.recOn  n
      x₀
      (fun n x => (r n).𝔼 (f n x))
    =
    (Nat.recOn (motive:=fun n => Rand (C n)) n
      (pure x₀)
      (fun n x => do
        let x' ← x
        let y' ← r n
        pure (f n x' y'))).mean := by unfold Nat.recOn; apply pull_E_nat_rec; assumption


end Nat

section List

variable {α}
  (C : List α → Type) [∀ n, AddCommGroup (C n)] [∀ n, Module ℝ (C n)] [∀ n, TopologicalSpace (C n)]
  [∀ n, MeasurableSpace (C n)] [∀ n, MeasurableSingletonClass (C n)]
  {D : List α → Type} [∀ n, MeasurableSpace (D n)]


@[rand_pull_E]
theorem pull_E_list_rec (l : List α) (x₀ : C [])
    (r : (head : α) → (tail : List α) → Rand (D (head::tail)))
    (f : (head : α) → (tail : List α) → C tail → D (head :: tail) → (C (head :: tail)))
    (hf : ∀ head tail d, IsAffineMap ℝ (f head tail · d)) :
    List.rec
      x₀
      (fun head tail x => (r head tail).𝔼 (f head tail x)) l
    =
    (List.rec (motive:=fun l => Rand (C l))
      (pure x₀)
      (fun head tail x => do
        let x' ← x
        let y' ← r head tail
        pure (f head tail x' y')) l).mean := by
  induction l
  case nil => simp[mean]
  case cons _ head tail hn =>
    simp[hn,mean]
    conv => simp[rand_pull_E,map]
    conv =>
      lhs
      enter[1,2,x',1]
      unfold mean
      simp[pull_E_affine (f:=(f head tail · x'))]
    conv =>
      simp[rand_pull_E]
    rw[Rand.swap_bind]


@[rand_pull_E]
theorem pull_E_list_recOn (l : List α) (x₀ : C [])
    (r : (head : α) → (tail : List α) → Rand (D (head::tail)))
    (f : (head : α) → (tail : List α) → C tail → D (head :: tail) → (C (head :: tail)))
    (hf : ∀ head tail d, IsAffineMap ℝ (f head tail · d)) :
    List.recOn l
      x₀
      (fun head tail x => (r head tail).𝔼 (f head tail x))
    =
    (List.recOn (motive:=fun l => Rand (C l)) l
      (pure x₀)
      (fun head tail x => do
        let x' ← x
        let y' ← r head tail
        pure (f head tail x' y'))).mean := by unfold List.recOn; apply pull_E_list_rec; assumption

end List
