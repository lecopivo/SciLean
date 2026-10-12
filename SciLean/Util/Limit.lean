module

public import Mathlib.Topology.Basic
public import SciLean.Util.SorryProof
public import Mathlib.Analysis.Calculus.FDeriv.Basic

@[expose] public section


noncomputable
def _root_.Filter.limit {β} [TopologicalSpace β] [Nonempty β]
  (l : Filter α) (f : α → β) : β := Filter.lim (l.map f)

/-- Note: the limit is unique only in a Hausdorff space and only along a non-trivial filter, hence
the added assumptions `[T2Space β]` and `[l.NeBot]`. -/
@[simp]
theorem Filter.limit_of_const {β} [TopologicalSpace β] [T2Space β] [Nonempty β]
  (l : Filter α) [l.NeBot] (b : β)
  : limit l (fun _ => b) = b :=
  lim_eq (by rw [Filter.map_const]; exact pure_le_nhds b)


-- Note: the limit is unique only in a Hausdorff space, hence the added assumption `[T2Space β]`.
set_option linter.unusedVariables false in
theorem Filter.limit_of_continuous {α β} [TopologicalSpace α] [TopologicalSpace β] [T2Space β]
  [Nonempty β]
  (a : α) (f : α → β) (hf : Continuous f)
  : limit (nhds a) f = f a :=
  lim_eq (hf.tendsto a)


namespace SciLean
open Lean.Parser.Term
scoped macro "limit " n:funBinder " → " n':term ", " y:term : term => `((nhds $n').limit (fun $n => $y))
scoped macro "limit " n:funBinder " → " "∞" ", " y:term : term => `((Filter.atTop).limit (fun $n => $y))
scoped macro "limit " n:funBinder " ∈ " l:term ", " y:term : term => `(Filter.limit $l (fun $n => $y))


@[scoped app_unexpander Filter.limit]
meta def unexpandFilterLimit : Lean.PrettyPrinter.Unexpander

  | `($(_) Filter.atTop fun $n => $y) =>
    `(limit $n → ∞, $y)

  | `($(_) Filter.atTop fun $n $ns* => $y) =>
    `(limit $n → ∞, fun $ns* => $y)

  | `($(_) $l fun $n => $y) =>
    match l with
    | `(nhds $x) => `(limit $n → $x, $y)
    | _ => `(limit $n ∈ $l, $y)

  | `($(_) $l fun $n $ns* => $y) =>
    match l with
    | `(nhds $x) => `(limit $n → $x, fun $ns* => $y)
    | _ => `(limit $n ∈ $l, fun $ns* => $y)

  | _  => throw ()

end SciLean
