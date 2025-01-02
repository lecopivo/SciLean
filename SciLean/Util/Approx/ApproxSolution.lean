import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic

import SciLean.Util.Limit

set_option linter.unusedVariables false

namespace SciLean

inductive ApproxSolution {α : Type _} [TopologicalSpace α] [Nonempty α] : {N : Type _} → (lN : Filter N) → (spec : α → Prop) → Type _
| exact {spec : α → Prop}
    (impl : α)
    (h : spec impl)
    : ApproxSolution (⊤ : Filter Unit) spec

| approx {N M} {spec : α → Prop}
    (specₙ : N → α → Prop)
    (lN : Filter N) (lM : Filter M)
    (consistent : ∀ (aₙ : N → α), (∀ n, specₙ n (aₙ n)) → (∀ a, (a = limit n ∈ lN, aₙ n) → spec a))
    (convergence : ∀ (a' : N → M → α), (∀ n, specₙ n (limit m ∈ lM, a' n m)) → ∃ a, a = limit (n,m) ∈ lN ×ˢ lM, a' n m)
    (impl : (n : N) → ApproxSolution lM (specₙ n))
    : ApproxSolution (lN ×ˢ lM) spec


variable {α} [TopologicalSpace α] [Nonempty α]

@[inline]
def ApproxSolution.val {N} {lN : Filter N} {spec : α → Prop}
  (a : ApproxSolution lN spec) (p : N) : α :=
match a with
| exact impl _ => impl
| approx _ _ _ _ _ impl => (impl p.1).val p.2


noncomputable
def ApproxSolution.limit {N} {lN : Filter N} {spec : α → Prop}
  (a : ApproxSolution lN spec) : α :=
match a with
| exact impl _ => impl
| approx _ lN _ _ _ impl => limit n ∈ lN, (impl n).limit


theorem approx_consistency {N} {lN : Filter N} [T2Space α] {spec : α → Prop}
  (approx : ApproxSolution lN spec)
  : ∀ a, a = (limit n ∈ lN, approx.val n) → spec a :=
by
  induction approx
  case exact impl h =>
    simp[ApproxSolution.val]
    sorry_proof
    -- intro a h'
    -- have : Filter.NeBot (⊤ : Filter Unit) := sorry_proof
    -- rw[tendsto_nhds_unique (a:=a) (b:=impl) h']
    -- apply h
    -- aesop
  case approx specₙ lN lM consistent convergence impl hn =>
    simp[ApproxSolution.val]
    -- intro h
    let aₙ := λ n => lim (lM.map λ m => (impl n).val m)
    sorry_proof
    -- have haₙ : ∀ n, specₙ n (aₙ n) := λ n => hn n ((hasLimit_split h).1 n)
    -- simp[limit_split h]
    -- have aₙ_def : ∀ n,  limit lM (fun m => ApproxSolution.val (impl n) m) = aₙ n := by intro n; rfl
    -- conv => enter[1,2,n]; rw[aₙ_def]
    -- apply consistent aₙ haₙ (limit lN aₙ) _
    -- apply limit_tendsto
    -- apply (hasLimit_split h).2


-- This is likely not true as it is currently stated. We likely need some extra assumption in the `.approx` constructor
theorem approx_convergence {N} {lN : Filter N} {spec : α → Prop}
  (approx : ApproxSolution lN spec)
  : ∃ a, lN.Tendsto approx.val (nhds a) := sorry_proof
-- by
--   induction approx
--   case exact impl h => exact ⟨impl, sorry⟩
--   case approx specₙ lN lM consistent convergence impl hn =>
--     simp[ApproxSolution.val]
--     sorry
