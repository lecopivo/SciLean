import Lean
open Lean Elab Command Term

namespace SciLean
namespace NotationOverField


initialize currentFieldName : IO.Ref Name ← IO.mkRef default

elab "open_notation_over_field" K:ident : command => do
  currentFieldName.set K.getId
  Lean.Elab.Command.elabCommand <| ←
   `(open SciLean.NotationOverField)

macro "set_default_scalar " K:ident : command => `(open_notation_over_field $K)
