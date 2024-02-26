import SciLean.Core.Rand.Rand
import SciLean.Core.FunctionPropositions
import SciLean.Core.FloatAsReal
-- import SciLean.Modules.Prob.DRand
-- import SciLean.Modules.Prob.FDRand

namespace SciLean

variable
  {R} [RealScalar R]
  -- {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace R X] [CompleteSpace X] [MeasurableSpace X]
  -- {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedSpace R Y] [CompleteSpace Y] [MeasurableSpace Y]
  -- {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedSpace R Z] [CompleteSpace Z] [MeasurableSpace Z]
  {X : Type _} [MeasurableSpace X] [AddCommGroup X] [Module ℝ X]
  {Y : Type _} [AddCommGroup Y] [Module ℝ Y]
  {Z : Type _} [AddCommGroup Z] [Module ℝ Z]

open Rand

@[rand_pull_E]
theorem bind_pull_mean (x : Rand X) (f : X → Rand Y) :
    (x >>= (fun x' => pure (f x').mean)).mean
    =
    (x >>= f).mean := by simp[mean,E,pure,bind]

@[rand_push_E]
theorem ite_push_E {c} [Decidable c] (t e : Rand X) (φ : X → Y):
    (if c then t else e).E φ = (if c then t.E φ else e.E φ) := by
  if h : c then simp[h] else simp[h]

-- I don't think this is a desirable `rand_pull_E` theorem as it duplicates the if statement
-- @[rand_pull_E]
theorem ite_pull_E {c} [Decidable c] (t e : Rand X) (φ ψ : X → Y):
    (if c then t.E φ else e.E ψ) = (if c then t else e).E (if c then φ else ψ) := by
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
    (fun x => r.E (fun y => f x y))
    =
    r.E (fun y x => f x y) := sorry_proof

-- this has messed up universes
@[rand_push_E]
theorem push_E_lambda (r : Rand Y) (f : X → Y → Z) :
    r.E (fun y x => f x y)
    =
    (fun x => r.E (fun y => f x y)) := sorry_proof

-- can't be simp as it has variable head
theorem pull_E_affine (r : Rand X) (φ : X → Y)
    (f : Y → Z) (hf : IsAffineMap ℝ f := by fun_prop) :
    (f (r.E φ)) = r.E (fun x => f (φ x)) := by sorry_proof -- have := hf; sorry_proof

@[rand_push_E]
theorem push_E_affine (r : Rand X) (φ : X → Y)
    (f : Y → Z) (hf : IsAffineMap ℝ f := by fun_prop) :
    r.E (fun x => f (φ x)) = (f (r.E φ)) := by rw[pull_E_affine (hf:=hf)]


section Nat

variable
  (C : ℕ → Type) [∀ n, AddCommGroup (C n)] [∀ n, Module ℝ (C n)]
  (D : ℕ → Type) [∀ n, MeasurableSpace (D n)]


@[rand_pull_E]
theorem pull_E_nat_recOn (x₀ : C 0) (r : (n : Nat) → Rand (D n))
    (f : (n : ℕ) → C n → D n → (C (n+1))) (hf : ∀ n d, IsAffineMap ℝ (f n · d)) :
    Nat.recOn  n
      x₀
      (fun n x => (r n).E (f n x))
    =
    (Nat.recOn (motive:=fun n => Rand (C n)) n
      (pure x₀)
      (fun n x => do
        let x' ← x
        let y' ← r n
        pure (f n x' y'))).mean := by
  induction n
  case zero => simp[mean]
  case succ n hn =>
    simp[hn,mean]
    conv => simp[rand_pull_E]
    conv =>
      lhs
      enter[1,2,x',1]
      unfold mean
      simp[pull_E_affine (f:=(f n · x'))]
    conv =>
      simp[rand_pull_E]
    rw[Rand.swap_bind]


end Nat

section List

variable {α}
  {C : List α → Type} [∀ n, AddCommGroup (C n)] [∀ n, Module ℝ (C n)]
  {D : List α → Type} [∀ n, MeasurableSpace (D n)]


@[rand_pull_E]
theorem pull_E_list_recOn (l : List α) (x₀ : C [])
    (r : (head : α) → (tail : List α) → Rand (D (head::tail)))
    (f : (head : α) → (tail : List α) → C tail → D (head :: tail) → (C (head :: tail)))
    (hf : ∀ head tail d, IsAffineMap ℝ (f head tail · d)) :
    List.recOn l
      x₀
      (fun head tail x => (r head tail).E (f head tail x))
    =
    (List.recOn (motive:=fun l => Rand (C l)) l
      (pure x₀)
      (fun head tail x => do
        let x' ← x
        let y' ← r head tail
        pure (f head tail x' y'))).mean := by
  induction l
  case nil => simp[mean]
  case cons _ head tail hn =>
    simp[hn,mean]
    conv => simp[rand_pull_E]
    conv =>
      lhs
      enter[1,2,x',1]
      unfold mean
      simp[pull_E_affine (f:=(f head tail · x'))]
    conv =>
      simp[rand_pull_E]
    rw[Rand.swap_bind]

end List
