import SciLean.Core.Rand.Distributions.Flip
import SciLean.Core.Rand.Tactic
import SciLean.Tactic.ConvInduction

import Mathlib.Tactic.FieldSimp

open MeasureTheory ENNReal BigOperators Finset

namespace SciLean.Rand

variable {R} [RealScalar R] [MeasureSpace R] [BorelSpace R] [ToString R]

def foo (l : List R) (n : Nat) : R :=
  match n with
  | 0 => 0
  | n+1 => l.get! n + foo l n


def foo' (θ : R) (l : List R) (n : Nat) : Rand R :=
  derive_random_approx
    (foo l n)
  by
    induction n n' prev h
    . simp[foo]
    . simp[foo,h]
    simp[add_as_flip_E θ sorry_proof]
    rw[pull_E_nat_recOn (x₀:=_) (r:=_) (hf:=by fun_prop)]


#eval print_mean_variance (foo' 0.5 [1.0,2,3,4] 4) 1000 ""
#eval print_mean_variance (foo' 0.3 [4.0,3,2,1] 4) 1000 ""


def bar (l : List R) : R :=
  match l with
  | [] => 0
  | x :: xs => x + bar xs

def bar' (θ : R) (l : List R) : Rand R :=
  derive_random_approx
    (bar l)
  by
    induction_list l head tail prev h
    . simp[bar]
    . simp[bar,h]
      rw[add_as_flip_E θ sorry_proof]
    rw[pull_E_list_recOn (D:=fun _ => _) (l:=_) (x₀:=_) (r:=_) (hf:=by fun_prop)]


#eval print_mean_variance (bar' 0.5 [1.0,2,3,4]) 1000 ""
#eval print_mean_variance (bar' 0.3 [4.0,3,2,1]) 1000 ""


-- tail recursive version of
def foobar (l : List R) (acc : R := 0) : R :=
  match l with
  | [] => acc
  | x :: xs => foobar xs (acc + x)


@[fun_prop]
theorem foobar.arg_acc.IsAffineMap (l : List R) : IsAffineMap ℝ (fun acc => foobar l acc) := by
  induction l <;> (simp[foobar]; fun_prop)


def foobar' (θ : R) (l : List R) : Rand R := do
  let f ←
    derive_random_approx
      fun acc => foobar l acc
    by
      induction_list l head tail prev h
      . simp[foobar]
      . simp[foobar,h]
        conv =>
          enter [acc]
          rw[add_as_flip_E θ sorry_proof]
          rw[pull_E_affine (f:=prev) (hf:=by rw[←h]; fun_prop)]
      conv =>
        enter [3,head,tail,prev]
        rw[pull_E_lambda]
      rw[pull_E_list_recOn (D:=fun _ => Bool) (l:=l) (x₀:=_) (r:=fun _ _ => flip θ) (hf:=by fun_prop)]
  return f 0


#eval print_mean_variance (foobar' 0.5 [1.0,2,3,4]) 1000 ""
#eval print_mean_variance (foobar' 0.3 [4.0,3,2,1]) 1000 ""
