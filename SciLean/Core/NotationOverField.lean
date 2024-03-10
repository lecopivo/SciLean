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


syntax "currentScalar%" : term

macro_rules | `(currentScalar%) => Lean.Macro.throwError "\
  This expression is using notation requiring to know the default scalar type. \
  To set it, add this command somewhere to your file \
  \n\n set_current_scalar R\
  \n\n\
  where R is the desired scalar, usually ℝ or Float.\n\n\
  If you want to write code that is agnostic about the particular scalar \
  type then introduce a generic type R with instance of `RealScalar R` \
  \n\n  variable {R : Type _} [RealScalar R]\
  \n  set_current_scalar R\
  \n\n\
  TODO: write a doc page about writing field polymorphic code and add a link here"

macro "set_current_scalar" r:term : command =>
  `(local macro_rules | `(currentScalar%) => `($r))
