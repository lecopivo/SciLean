import SciLean.Core.Notation.CDeriv
import SciLean.Core.FunctionTransformations.RevCDeriv


--------------------------------------------------------------------------------
-- Notation  -------------------------------------------------------------------
--------------------------------------------------------------------------------

namespace SciLean.NotationOverField

scoped syntax "<∂ " term:66 : term
scoped syntax "<∂ " diffBinder ", " term:66 : term
scoped syntax "<∂ " "(" diffBinder ")" ", " term:66 : term

scoped syntax "<∂! " term:66 : term
scoped syntax "<∂! " diffBinder ", " term:66 : term
scoped syntax "<∂! " "(" diffBinder ")" ", " term:66 : term

open Lean Elab Term Meta in
elab_rules : term
| `(<∂ $f $xs*) => do
  let K := mkIdent (← currentFieldName.get)
  elabTerm (← `(revCDeriv $K $f $xs*)) none
| `(<∂ $f) => do
  let K := mkIdent (← currentFieldName.get)
  elabTerm (← `(revCDeriv $K $f)) none
| `(<∂ $x:ident := $val:term ; $codir:term, $b) => do
  let K := mkIdent (← currentFieldName.get)
  elabTerm (← `(revCDerivEval $K (fun $x => $b) $val $codir)) none

macro_rules
| `(<∂ $x:ident, $b) => `(<∂ (fun $x => $b))
| `(<∂ $x:ident := $val:term, $b) => `(<∂ (fun $x => $b) $val)
| `(<∂ $x:ident : $type:term, $b) => `(<∂ fun $x : $type => $b)
| `(<∂ ($b:diffBinder), $f)       => `(<∂ $b, $f)

macro_rules
| `(<∂! $f $xs*) => `((<∂ $f $xs*) rewrite_by ftrans; ftrans; ftrans)
| `(<∂! $f) => `((<∂ $f) rewrite_by ftrans; ftrans; ftrans)
| `(<∂! $x:ident, $b) => `(<∂! (fun $x => $b))
| `(<∂! $x:ident := $val:term, $b) => `(<∂! (fun $x => $b) $val)
| `(<∂! $x:ident : $type:term, $b) => `(<∂! fun $x : $type => $b)
| `(<∂! ($b:diffBinder), $f)       => `(<∂! $b, $f)


@[app_unexpander revCDeriv] def unexpandRevCDeriv : Lean.PrettyPrinter.Unexpander

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


@[app_unexpander revCDerivEval] def unexpandRevCDerivEval : Lean.PrettyPrinter.Unexpander

  | `($(_) $_ $f:term $x $dy) =>
    match f with
    | `(fun $x':ident => $b:term) => `(<∂ ($x':ident:=$x;$dy), $b)
    | `(fun ($x':ident : $_) => $b:term) => `(<∂ ($x':ident:=$x;$dy), $b)
    | _  => throw () 

  | _ => throw ()

end NotationOverField
