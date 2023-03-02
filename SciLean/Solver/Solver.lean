-- import SciLean.Operators
import SciLean.Core
-- import SciLean.Functions.OdeSolve
import SciLean.Tactic.BubbleLimit

namespace SciLean

inductive ExactSolution {α : Type _} : (spec : α → Prop) → Type _
| exact {spec : α → Prop}
        (a : α) (h : spec a)
        : ExactSolution spec

def ExactSolution.val {α} {spec : α → Prop} : ExactSolution spec → α 
| ExactSolution.exact a' _ => a'

-- inductive Parameter where
-- | fin (n : Nat) (m : Fin n) : Parameter
-- | nat (n : Nat) : Parameter
-- | int  (n : Int) : Parameter
-- | float (x : Float) : Parameter
-- | string (s : String) : Parameter

-- def Parameter.type : Parameter → Type
-- | fin n _ => Fin n
-- | nat _ => Nat
-- | int _ => Int
-- | float _ => Float
-- | string _ => String

-- def Parameter.val (p : Parameter) : p.type :=
-- match p with
-- | fin _ m => m
-- | nat n => n
-- | int n => n
-- | float x => x
-- | string s => s

-- This might not be provable as `Fin n = Fin m` does not imply `n = m`
-- instance (p p' : Parameter) : Decidable (p.type = p'.type) :=
-- match p, p' with
-- | .fin n _, .fin n' _ => if h : n = n' then isTrue (by simp[Parameter.type]; rw[h]) else isFalse sorry
-- | .nat _, .nat _ => isTrue (by rfl) 
-- | .int _, .int _ => isTrue (by rfl) 
-- | .float _, .float _ => isTrue (by rfl)
-- | .string _, .string _ => isTrue (by rfl)
-- | _, _ => isFalse sorry

inductive ApproxSolution {α : Type _} : (spec : α → Prop) → Type _ 
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
-- | approx' {spec : α → Prop}
--     (specₙ : P → α → Prop)
--     (filter : Filter P)
--     (consistent : ∀ (aₙ : P → α),
--       (∀ p, specₙ p (aₙ p)) →
--       (∃ a, (lim filter aₙ = a) → spec a))
--     (p₀ : P) -- default value of `n` to be used when asembling
--     (impl : P → α)
--     (h : ∀ p, specₙ p (impl p))
--     (key help : String) -- `key` is used to modify value of `n₀`
--     : ApproxSolution spec
| /--
  There exists a limiting process but we are going to provide only fixed
approximation
 -/
 weakApprox {spec : α → Prop}
    (specₙ : ℕ → α → Prop)
    (consistent : ∀ (aₙ : ℕ → α),
      (∀ n, specₙ n (aₙ n)) →
      (∃ a, (limit aₙ = a) → spec a))
    (n : ℕ) -- fixed aproximation at compile time
    (impl : ApproxSolution (specₙ n))
    (help : String)
    : ApproxSolution spec
-- | param {spec : α → Prop} {β : Type}
--     (impl : β → ApproxSolution spec)
--     (p : Parameter)
--     (h : p.type = β)
--     (key : String)
--     (help : String)
--     : ApproxSolution spec
-- | check {spec : α → Prop}
--     {P : Prop} [dec : Decidable P]
--     (impl : P → ApproxSolution spec)
--     (help : String)
--     : ApproxSolution spec
-- | assumption {spec : α → Prop}
--     {P : Prop}
--     (impl : P → ApproxSolution spec)
--     (help : String)
--     : ApproxSolution spec

def ApproxSolution.val {α} {spec : α → Prop} : ApproxSolution spec → α 
| exact impl _ => impl
| approx _ _ n impl _ _ => (impl n).val
-- | param impl p h _ _ => (impl (h ▸ p.val)).val!
| weakApprox _ _ _ impl _ => impl.val
-- | check      impl _ => (impl sorry).val!
-- | assumption impl _ => (impl sorry).val!

-- def ApproxSolution.changeParam {α} [Vec α] {spec : α → Prop} 
--   (p : Parameter) (key : String) 
--   : ApproxSolution spec → ApproxSolution spec
-- | exact impl h => exact impl h
-- | approx _ h n impl key' help => approx _ h n (λ n => (impl n).changeParam p key) key' help
-- | weakApprox _ h n impl help => weakApprox _ h n (impl.changeParam p key) help
-- | param impl p' h key' help => 
--   if key = key' then
--     if p.type = p'.type then
--       param impl p' h key' help
--     else
--       param (λ p' => (impl p').changeParam p key) p' h key' help
--   else
--     param (λ p' => (impl p').changeParam p key) p' h key' help
-- | check impl help => check (λ h => (impl h).changeParam p key) help
-- | assumption impl help => assumption (λ h => (impl h).changeParam p key) help
-- | e => e

----------------------------------------------------------------------

-- def Impl {α} (a : α) := ExactSolution (λ x => x = a)
-- def Impl.val {α} {a : α} (impl : Impl a) : α := ExactSolution.val impl
-- def Impl.exact {a : α} : Impl a := ExactSolution.exact a rfl

-- @[simp]
-- theorem Impl.impl_eq_spec (x : Impl a) : x.val = a :=
-- by
--   cases x; rename_i a' h; 
--   simp[ExactSolution.val, val, h]
--   done


def Approx {α} (a : α) := ApproxSolution (λ x => x = a)
def Approx.val {α} {a : α} (approx : Approx a) : α := ApproxSolution.val approx
def Approx.exact {α} {a : α} : Approx a := ApproxSolution.exact a rfl
def Approx.limit {α} {aₙ : ℕ → α} (x : (n : ℕ) → Approx (aₙ n)) (n₀ : ℕ)
  : Approx (limit aₙ) := ApproxSolution.approx (λ n x => x = (aₙ n)) sorry n₀ x "" "" 


-- instance {α} (a : α) : Coe (Approx a) α := ⟨λ approx => approx.val⟩
instance {α β : Type _} (f : α → β) : CoeFun (Approx f) (λ _ => α → β) := ⟨λ approx => approx.val⟩

syntax declModifiers "approx " declId bracketedBinder* (":" term)? ":=" term " by " tacticSeq : command

macro_rules
  | `($mods:declModifiers approx $id $params:bracketedBinder* := $body by $rewrites:tacticSeq) =>
    `($mods:declModifiers def $id $params:bracketedBinder* := (by ($rewrites); (apply Approx.exact) : Approx $body))


-- def foo (s : ℝ) := ∇ (λ x : ℝ => s * x)
-- rewrite_by
--   simp[gradient]

-- Add proof and 
macro "approx_limit " n0:term : tactic =>
 `(tactic| ((conv => enter [1]; bubble_lim; (tactic => sorry)); apply (Approx.limit _ ($n0:term))))

approx bar (s : ℝ) (n₀ : ℕ) := ∇ (limit λ n => λ x : ℝ => (s + (1:ℝ)/(n:ℝ)) * x)
by
  approx_limit n₀; intro n;
  symdiff



