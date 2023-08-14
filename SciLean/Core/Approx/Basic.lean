import SciLean.Core.Approx.ApproxSolution
import Mathlib.Analysis.Calculus.FDeriv.Basic

namespace SciLean

abbrev Approx  {N : outParam $ Type _} (lN : Filter N) {α} [TopologicalSpace α] (a : α)  := ApproxSolution lN (fun x => a=x)

abbrev Approx.exact {α} [TopologicalSpace α] {a : α} := ApproxSolution.exact a rfl
def Approx.limit {N M α} [TopologicalSpace α] [Nonempty α] (lN : Filter N) (lM : Filter M) {aₙ : N → α} (x : (n : N) → Approx lM (aₙ n)) 
  : Approx (lN.prod lM) (lim (lN.map aₙ)) := ApproxSolution.approx (λ n x => (aₙ n)=x) lN lM sorry sorry x


instance {N α} [TopologicalSpace α] (lN : Filter N) (a : α) : CoeFun (Approx (lN:=lN) a) (λ _ => N → α) := ⟨λ approx => approx.val⟩

syntax declModifiers "approx " declId bracketedBinder* (":" term)? ":=" term " by " tacticSeq : command

open Lean Elab Term Command in
elab_rules : command
  | `($mods:declModifiers approx $id $params:bracketedBinder* := $body by $rewrites:tacticSeq) => do
    elabCommand (← `($mods:declModifiers def $id $params:bracketedBinder* := (by ($rewrites); (try apply Approx.exact) : Approx _ $body)))
