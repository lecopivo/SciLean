import Lean
import Mathlib.Logic.Nonempty
import SciLean.Lean.Meta.Basic

namespace SciLean


attribute [local instance] Classical.propDecidable

noncomputable
def solveFun {α : Type _} [Nonempty α] (P : α → Prop) : α :=
  if h : (∃ a, P a) then
    Classical.choose h
  else
    Classical.arbitrary α


open Lean Parser Elab Term in
elab "solve" xs:funBinder* ", " b:term : term => do
  let stx ← `(fun $xs* => $b)
  let f ← elabTerm stx.raw none
  Meta.mkAppM ``solveFun #[← Meta.mkUncurryFun xs.size f]
