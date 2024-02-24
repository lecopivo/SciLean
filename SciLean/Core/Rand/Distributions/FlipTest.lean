import SciLean.Core.Rand.Distributions.Flip
import SciLean.Core.Rand.Tactic
import SciLean.Tactic.ConvInduction

import Mathlib.Tactic.FieldSimp

open MeasureTheory ENNReal BigOperators Finset

namespace SciLean.Prob

variable {R} [RealScalar R] [ToString R]


def test (θ : R) : Rand R := do
  let b ← flip θ
  if b then
    pure 0
  else
    pure (-θ/2)

def test_mean (θ : R) := (test θ).mean
  rewrite_by
    unfold test
    simp[rand_push_E,flip.E]

#eval show IO Unit from do

  let θ : Float := 0.8
  let n := 1000
  let mut m : Float := 0
  for _ in [0:n] do
    if (← (flip θ).get) then
      m := m+1

  m := m/n
  IO.println s!"estimate: {m}"


def foo (l : List R) (n : Nat) : R :=
  match n with
  | 0 => 0
  | n+1 => l.get! n + foo l n

#eval foo [1.0,2,3] 3

#check Rand.expectedValue_as_mean
def foo' (θ : R) (l : List R) (n : Nat) : Rand R :=
  derive_random_approx
    (foo l n)
  by
    induction n n' prev h
    . simp[foo]
    . simp[foo,h]
      rw[add_as_flip_E θ sorry_proof]
    rw[pull_E_nat_recOn (x₀:=_) (r:=_) (hf:=by fun_prop)]


#eval print_mean_variance (foo' 0.5 [1.0,2,3,4] 4) 1000 ""
#eval print_mean_variance (foo' 0.3 [4.0,3,2,1] 4) 1000 ""


def bar (l : List R) : R :=
  match l with
  | [] => 0
  | x :: xs => x + bar xs

#eval bar [1.0,2,3]

def bar' (θ : R) (l : List R) : Rand R :=
  derive_random_approx
    (bar l)
  by
    induction_list l head tail prev h
    . simp[bar]
    . simp[bar,h]
      rw[add_as_flip_E θ sorry_proof]
    rw[pull_E_list_recOn (D:=fun _ => Bool) (l:=_) (x₀:=_) (r:=_) (hf:=by fun_prop)]


#eval print_mean_variance (bar' 0.5 [1.0,2,3,4]) 1000 ""
#eval print_mean_variance (bar' 0.3 [4.0,3,2,1]) 1000 ""


-- tail recursive version of
def foobar (l : List R) (acc : R := 0) : R :=
  match l with
  | [] => 0
  | x :: xs => foobar xs (acc + x)

#eval foobar [1.0,2,3]

@[fun_prop]
theorem foobar.arg_acc.IsAffineMap (l : List R) : IsAffineMap ℝ (fun acc => foobar l acc) := by
  induction l <;> (simp[foobar]; fun_prop)


def foobar' (θ : R) (l : List R) : Rand R :=
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
          -- rw[pull_E_list_recOn (D:=fun _ => Bool) (l:=_) (x₀:=fun _ => 0) (r:=fun _ _ => flip θ) (hf:=by fun_prop)]
