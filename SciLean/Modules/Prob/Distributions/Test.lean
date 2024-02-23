import SciLean.Modules.Prob.Tactic
import SciLean.Modules.Prob.Distributions.Flip
import SciLean.Tactic.ConvInduction

import Mathlib.Tactic.FieldSimp

import SciLean.Core.FunctionPropositions

import Mathlib.Lean.Expr

open MeasureTheory ENNReal BigOperators Finset Measure

namespace SciLean.Prob

open Rand
variable {R} [RealScalar R]

variable
  [NormedAddCommGroup X] [NormedSpace R X] [NormedSpace ℝ X] [CompleteSpace X] [MeasurableSpace X]
  [NormedAddCommGroup Y] [NormedSpace R Y] [NormedSpace ℝ Y] [CompleteSpace Y] [MeasurableSpace Y]
  [NormedAddCommGroup Z] [NormedSpace R Z] [NormedSpace ℝ Z] [CompleteSpace Z] [MeasurableSpace Z]


variable (C : ℕ → Type) [∀ n, NormedAddCommGroup (C n)] [∀ n, NormedSpace ℝ (C n)] [∀ n, CompleteSpace (C n)] [∀ n, MeasurableSpace (C n)]
variable (D : ℕ → Type) [∀ n, NormedAddCommGroup (D n)] [∀ n, NormedSpace ℝ (D n)] [∀ n, CompleteSpace (D n)] [∀ n, MeasurableSpace (D n)]


-- this needs some integrability
theorem swap_bind (f : X → Y → Z) (x : Rand X) (y : Rand Y) :
    (let x' ~ x; let y' ~ y; pure (f x' y'))
    =
    (let y' ~ y; let x' ~ x; pure (f x' y')) := sorry

-- this requires that `f` is affine
theorem push_to_E' (f : X → Y) (hf : IsAffineMap ℝ f) (r : Rand Z) (φ : Z → X) :
    (f (r.E φ)) = r.E (fun z => f (φ z)) := sorry

@[rand_pull_E]
theorem E_induction (x₀ : C 0) (r : (n : Nat) → Rand (D n)) (f : (n : ℕ) → C n → D n → (C (n+1))) :
    Nat.recOn (motive:=C) n
      x₀
      (fun n x => (r n).E (f n x))
    =
    (Nat.recOn (motive:=fun n => Rand (C n)) n
      (pure x₀)
      (fun n x =>
        let x' ~ x;
        let y' ~ r n;
        pure (f n x' y'))).mean := by
  induction n
  case zero => simp[mean]
  case succ n hn =>
    simp[hn,mean]
    conv => rand_pull_E
    simp
    conv =>
      lhs
      enter[1,2,x',1]
      unfold mean
      simp[push_to_E' (f:=(f n · x')) (hf:=by sorry)]
    conv =>
      rand_pull_E
    rw[swap_bind]


theorem add_as_flip_mean (θ : R) {x y : X} :
    x + y = (flip θ).E (fun b => if b then θ⁻¹ • x else (1-θ)⁻¹ • y) := sorry

def foo (l : List R) (n : Nat) : R :=
  match n with
  | 0 => 0
  | n+1 => l.get! n + foo l n

#eval foo [1.0,2,3] 3

def foo' (θ : R) (l : List R) (n : Nat) : Rand R :=
  derive_random_approx
    (foo l n)
  by
    induction n n' prev h
    . simp[foo]
    . simp[foo,h]
      rw[add_as_flip_mean θ]
    rw[E_induction]


#eval print_mean_variance1 (foo' 0.5 [1.0,2,3,4] 4) 1000 ""

#eval print_mean_variance1 (foo' 0.3 [4.0,3,2,1] 4) 1000 ""
