import SciLean.Data.IndexType.Range
import SciLean.Data.Idx.Basic


namespace SciLean

syntax:max (name:=idxRangeFull) (priority:=high) "[" withoutPosition(":" term) "]" : term
-- syntax:max (name:=idxRangeInterval) (priority:=high) "[" withoutPosition(term ":" term) "]" : term

open Lean Elab Term Qq Meta in
elab_rules (kind:=idxRangeFull) : term
  | `([ : $n]) => do
    -- make full range over `Idx n` if `n` is `Nat`
    try
      let n ← elabTerm n q(Nat)
      let r ← mkAppOptM  ``IndexType.Range.full #[← mkAppM ``Idx #[n]]
      return r
    catch _ =>
      let I ← elabTerm n none
      let r ← mkAppOptM ``IndexType.Range.full #[I]
      return r
