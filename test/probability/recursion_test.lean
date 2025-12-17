import SciLean.Probability.Distributions.Flip
import SciLean.Probability.Tactic
import SciLean.Tactic.ConvInduction

import SciLean.Analysis.Scalar.FloatAsReal

import Mathlib.Tactic.FieldSimp

open MeasureTheory ENNReal BigOperators Finset

open SciLean Rand

set_option deprecated.oldSectionVars true
variable {R} [RealScalar R] [MeasureSpace R] [BorelSpace R] [ToString R]

local instance [Zero R] : Inhabited R := ⟨0⟩

def list_sum1 (l : List R) (n : Nat) : R :=
  match n with
  | 0 => 0
  | n+1 => l.get! n + list_sum1 l n


def list_sum1_estimator (θ : R) (l : List R) (n : Nat) : Rand R :=
  derive_random_approx
    (list_sum1 l n)
  by
    induction n n' prev h
    . simp[list_sum1]
    . simp[list_sum1,h]
    simp[add_as_flip_E θ sorry_proof]

    rw[pull_E_nat_rec (x₀:=_) (r:=_) (hf:=by fun_prop)]


-- #eval print_mean_variance (list_sum1_estimator 0.5 [1.0,2,3,4] 4) 1000 ""
-- #eval print_mean_variance (list_sum1_estimator 0.3 [4.0,3,2,1] 4) 1000 ""


def list_sum2 (l : List R) : R :=
  match l with
  | [] => 0
  | x :: xs => x + list_sum2 xs

def list_sum2_estimator (θ : R) (l : List R) : Rand R :=
  derive_random_approx
    (list_sum2 l)
  by
    induction_list l head tail prev h
    . simp[list_sum2]
    . simp[list_sum2,h]
      rw[add_as_flip_E θ sorry_proof]
    rw[pull_E_list_recOn (D:=fun _ => _) (l:=_) (x₀:=_) (r:=_) (hf:=by fun_prop)]


-- #eval print_mean_variance (list_sum2_estimator 0.5 [1.0,2,3,4]) 1000 ""
-- #eval print_mean_variance (list_sum2_estimator 0.3 [4.0,3,2,1]) 1000 ""


-- tail recursive version of
def list_sum3 (l : List R) (acc : R := 0) : R :=
  match l with
  | [] => acc
  | x :: xs => list_sum3 xs (acc + x)


open MeasureTheory in
-- is this true?
instance [MeasurableSpace β] [MeasurableSingletonClass β] :
  MeasurableSingletonClass (α → β) := sorry_proof

@[fun_prop]
theorem list_sum3.arg_acc.IsAffineMap (l : List R) :
    IsAffineMap ℝ (fun acc => list_sum3 l acc) := by
  induction l <;> (simp[list_sum3]; fun_prop)


def list_sum3_estimator (θ : R) (l : List R) : Rand R := do
  let f ←
    derive_random_approx
      fun acc => list_sum3 l acc
    by
      induction_list l head tail prev h
      . simp[list_sum3]
      . simp[list_sum3,h]
        conv =>
          enter [acc]
          rw[add_as_flip_E θ sorry_proof]
          rw[pull_E_affine (f:=prev) (hf:=by rw[←h]; fun_prop)]
      conv =>
        enter [3,head,tail,prev]
        rw[pull_E_lambda]
      rw[pull_E_list_recOn (D:=fun _ => Bool) (l:=l) (x₀:=_)
                           (r:=fun _ _ => flip θ) (hf:=by fun_prop)]
  return f 0


-- #eval print_mean_variance (list_sum3_estimator 0.5 [1.0,2,3,4]) 1000 ""
-- #eval print_mean_variance (list_sum3_estimator 0.3 [4.0,3,2,1]) 1000 ""
