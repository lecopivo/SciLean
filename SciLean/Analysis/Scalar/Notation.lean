import Lean
open Lean Elab Command Term

namespace SciLean
namespace NotationOverField

syntax "defaultScalar%" : term

macro_rules | `(defaultScalar%) => show MacroM (TSyntax `term) from
  Lean.Macro.throwError "\
  This expression is using notation requiring to know the default scalar type. \
  To set it, add this command somewhere to your file \
  \n\n set_default_scalar R\
  \n\n\
  where R is the desired scalar, usually ℝ or Float.\n\n\
  If you want to write code that is agnostic about the particular scalar \
  type then introduce a generic type R with instance of `RealScalar R` \
  \n\n  variable {R : Type _} [RealScalar R]\
  \n  set_default_scalar R\
  \n\n\
  TODO: write a doc page about writing field polymorphic code and add a link here"

macro "set_default_scalar" r:term : command =>
  `(local macro_rules | `(defaultScalar%) => do pure (← `($r)).raw)
