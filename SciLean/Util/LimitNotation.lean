import Mathlib.Topology.Basic
import SciLean.Util.SorryProof
import Mathlib.Analysis.Calculus.FDeriv.Basic

noncomputable
def _root_.Filter.limit {β} [TopologicalSpace β] [Nonempty β] 
  (l : Filter α) (f : α → β) : β := lim (l.map f)

@[simp]
theorem Filter.limit_of_const {β} [TopologicalSpace β] [Nonempty β] 
  (l : Filter α) (b : β) 
  : limit l (fun _ => b) = b := sorry_proof

namespace LimitNotation 
open Lean.Parser.Term
scoped macro " limit " n:funBinder " → " n':term ", " y:term : term => `((nhds $n').limit (fun $n => $y))
scoped macro " limit " n:funBinder " → " "∞" ", " y:term : term => `((Filter.atTop).limit (fun $n => $y))
scoped macro " limit " n:funBinder " ∈ " l:term ", " y:term : term => `(Filter.limit $l (fun $n => $y))


@[app_unexpander Filter.limit] def unexpandFilterLimit : Lean.PrettyPrinter.Unexpander

  | `($(_) Filter.atTop fun $n => $y) =>
    `(limit $n → ∞, $y)
  | `($(_) $l fun $n => $y) =>
    match l with
    | `(nhds $x) => `(limit $n → $x, $y)
    | _ => `(limit $n ∈ $l, $y)
  | _  => throw ()

end LimitNotation



