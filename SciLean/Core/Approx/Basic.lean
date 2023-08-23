-- TODO: minimize this import
import Mathlib.Analysis.Calculus.FDeriv.Basic

import SciLean.Core.Approx.ApproxSolution
import SciLean.Util.Limit
import SciLean.Util.SorryProof

namespace SciLean

open LimitNotation

abbrev Approx  {N : outParam $ Type _} (lN : Filter N) {α} [TopologicalSpace α] (a : α)  := ApproxSolution lN (fun x => a=x)

abbrev Approx.exact {α} [TopologicalSpace α] {a : α} := ApproxSolution.exact a rfl
abbrev Approx.limit {N} {lN : Filter N} (M) (lM : Filter M) 
  {α} [TopologicalSpace α] [Nonempty α] {aₙ : N → α} (x : (n : N) → Approx lM (aₙ n)) 
  : Approx (lN.prod lM) (limit n ∈ lN, aₙ n) := 
  ApproxSolution.approx _ lN lM 
    (by intro aₙ' h a h'; simp[h,h'])
    (by sorry_proof)
    x


instance {N α} [TopologicalSpace α] (lN : Filter N) (a : α) : CoeFun (Approx (lN:=lN) a) (λ _ => N → α) := ⟨λ approx => approx.val⟩

syntax declModifiers "approx " declId bracketedBinder* (":" term)? ":=" term " by " tacticSeq : command

open Lean Elab Term Command in
elab_rules : command
  | `($mods:declModifiers approx $id $params:bracketedBinder* := $body by $rewrites:tacticSeq) => do
    elabCommand (← `($mods:declModifiers def $id $params:bracketedBinder* := (by ($rewrites); (try apply Approx.exact) : Approx _ $body)))
