import SciLean.Operators
import SciLean.Tactic.BubbleLimit

namespace SciLean

inductive ExactSolution {α : Type _} : (spec : α → Prop) → Type _
| exact {spec : α → Prop}
        (a : α) (h : spec a)
        : ExactSolution spec

def ExactSolution.val {α} {spec : α → Prop} : ExactSolution spec → α 
| ExactSolution.exact a' _ => a'

inductive ApproxSolution {α : Type _} [Vec α] : (spec : α → Prop) → Type _ 
| exact {spec : α → Prop}
    (impl : α)
    (h : spec impl)
    : ApproxSolution spec
| approx {spec : α → Prop}
    (specₙ : ℕ → α → Prop)
    (consistent : ∀ (aₙ : ℕ → α),
      (∀ n, specₙ n (aₙ n)) →
      (∃ a, (limit aₙ = a) → spec a))
    (n₀ : ℕ) -- default value of `n` to be used when asembling
    (impl : (n : ℕ) → ApproxSolution (specₙ n))
    (key help : String) -- `key` is used to modify value of `n₀`
    : ApproxSolution spec
| weakApprox {spec : α → Prop}
    (specₙ : ℕ → α → Prop)
    (consistent : ∀ (aₙ : ℕ → α),
      (∀ n, specₙ n (aₙ n)) →
      (∃ a, (limit aₙ = a) → spec a))
    (n : ℕ) -- fixed aproximation at compile time
    (impl : ApproxSolution (specₙ n))
    (help : String)
    : ApproxSolution spec
| check {spec : α → Prop}
    {P : Prop} [dec : Decidable P]
    (impl : P → ApproxSolution spec)
    (help : String)
    : ApproxSolution spec
| assumption {spec : α → Prop}
    {P : Prop}
    (impl : P → ApproxSolution spec)
    (help : String)
    : ApproxSolution spec

def ApproxSolution.val! {α} [Vec α] {spec : α → Prop} : ApproxSolution spec → α 
| exact impl _ => impl
| approx _ _ n impl key _ => (impl n).val!
| weakApprox _ _ _ impl _ => impl.val!
| check      impl _ => (impl sorry).val!
| assumption impl _ => (impl sorry).val!

----------------------------------------------------------------------

def Impl {α} (a : α) := ExactSolution (λ x => x = a)
def Impl.val {α} {a : α} (impl : Impl a) : α := ExactSolution.val impl
def Impl.exact {a : α} : Impl a := ExactSolution.exact a rfl

@[simp]
theorem Impl.impl_eq_spec (x : Impl a) : x.val = a :=
by
  cases x; rename_i a' h; 
  simp[ExactSolution.val, val, h]
  done


open Lean.Parser.Tactic.Conv

syntax declModifiers "def " declId bracketedBinder* (":" term)? ":=" term " optimize " convSeq : command
syntax declModifiers "def " declId bracketedBinder* (":" term)? ":=" term " rewrite " convSeq : command

macro_rules
  | `($mods:declModifiers def $id $params:bracketedBinder* $[: $ty:term]? := $body optimize $opt:convSeq) =>
    `($mods:declModifiers def $id $params:bracketedBinder* $[: $ty]? := (by (conv => enter[1]; $opt) (apply Impl.exact) : Impl $body).val)
  | `($mods:declModifiers def $id $params:bracketedBinder* $[: $ty:term]? := $body rewrite $opt:convSeq) =>
    `($mods:declModifiers def $id $params:bracketedBinder* $[: $ty:term]? := $body optimize $opt:convSeq)

-- TODO: move this 
namespace Impl.Tests
  def foo : Nat → Nat := 
    dbg_trace "Calling foo!"
    λ n => n

  def bar (n : Nat) : Nat := foo n

  def bar_opt (n : Nat) : Nat := foo n
  optimize
    simp[foo, dbgTrace]

  theorem bar_opt_eq_foo : bar_opt = foo := 
  by
    simp[bar_opt]

  #eval bar 10
  #eval bar_opt 10
end Impl.Tests
----------------------------------------------------------------------

def Approx {α} [Vec α] (a : α) := ApproxSolution (λ x => x = a)
def Approx.val! {α} [Vec α] {a : α} (approx : Approx a) : α := ApproxSolution.val! approx
def Approx.exact {α} [Vec α] {a : α} : Approx a := ApproxSolution.exact a rfl
def Approx.limit {α} [Vec α] {aₙ : ℕ → α} (x : (n : ℕ) → Approx (aₙ n)) (n₀ : ℕ)
  : Approx (limit aₙ) := ApproxSolution.approx (λ n x => x = (aₙ n)) sorry n₀ x "" "" 


syntax declModifiers "approx " declId bracketedBinder* (":" term)? ":=" term " by " tacticSeq : command

macro_rules
  | `($mods:declModifiers approx $id $params:bracketedBinder* := $body by $rewrites:tacticSeq) =>
    `($mods:declModifiers def $id $params:bracketedBinder* := (by ($rewrites) (apply Approx.exact) : Approx $body))


def foo (s : ℝ) := ∇ (λ x : ℝ => s * x)
rewrite
  simp[gradient, adjoint_differential]


approx bar (s : ℝ) (n₀ : ℕ) := ∇ (limit λ n => λ x : ℝ => (s + 1.0/(n:ℝ)) * x)
by
  conv => enter [1]; bubble_lim; (tactic => admit)
  apply Approx.limit _ n₀; intro n
  simp[gradient, adjoint_differential]

 
#eval foo 10 1
#eval (bar 10 100).val! 1

#check Monad
#check @Approx


-- ApproxSolution

-- Approx a := ApproxSolution (λ x => x = a) 
-- Impl a := ExactSolution (λ x => x = a)
