import SciLean.Analysis.Calculus.Notation.Deriv
import SciLean.Analysis.Calculus.RevFDeriv


--------------------------------------------------------------------------------
-- Notation  -------------------------------------------------------------------
--------------------------------------------------------------------------------

namespace SciLean.Notation

syntax "<∂ " term:66 : term
syntax "<∂ " diffBinder ", " term:66 : term
syntax "<∂ " "(" diffBinder ")" ", " term:66 : term

syntax "<∂! " term:66 : term
syntax "<∂! " diffBinder ", " term:66 : term
syntax "<∂! " "(" diffBinder ")" ", " term:66 : term

open Lean Elab Term Meta in
elab_rules : term
| `(<∂ $f $x $xs*) => do
  let X ← inferType (← elabTerm x none)
  let sX ← exprToSyntax X
  elabTerm (← `(revFDeriv (X:=$sX) defaultScalar% $f $x $xs*)) none
| `(<∂ $f) => do
  elabTerm (← `(revFDeriv defaultScalar% $f)) none

macro_rules
| `(<∂ $x:term, $b) => `(<∂ (fun $x => $b))
| `(<∂ $x:term : $type:term, $b) => `(<∂ fun $x : $type => $b)
| `(<∂ $x:term := $val:term, $b) => `(<∂ (fun $x => $b) $val)
-- with brackets
| `(<∂ ($x:term := $val:term), $b) => `(<∂ (fun $x => $b) $val)


macro_rules
| `(<∂! $f $xs*) => `((<∂ $f $xs*) rewrite_by autodiff)
| `(<∂! $f) => `((<∂ $f) rewrite_by autodiff)
| `(<∂! $x:term, $b) => `(<∂! (fun $x => $b))
| `(<∂! $x:term : $type:term, $b) => `(<∂! fun $x : $type => $b)
| `(<∂! $x:term := $val:term, $b) => `(<∂! (fun $x => $b) $val)
-- with brackets
| `(<∂! ($x:term := $val:term), $b) => `(<∂! (fun $x => $b) $val)


@[app_unexpander revFDeriv] def unexpandRevFDeriv : Lean.PrettyPrinter.Unexpander

  | `($(_) $_ $f:term $x) =>
    match f with
    | `(fun $x':ident => $b:term) => `(<∂ ($x':ident:=$x), $b)
    | `(fun ($x':ident : $_) => $b:term) => `(<∂ ($x':ident:=$x), $b)
    | _  => `(<∂ $f:term $x)

  | `($(_) $_ $f:term) =>
    match f with
    | `(fun $x':ident => $b:term) => `(<∂ $x':ident, $b)
    | `(fun ($x':ident : $ty) => $b:term) => `(<∂ ($x' : $ty), $b)
    | _  => `(<∂ $f)

  | _  => throw ()
