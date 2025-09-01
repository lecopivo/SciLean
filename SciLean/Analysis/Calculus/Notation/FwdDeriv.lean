import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Analysis.Calculus.Notation.Deriv


--------------------------------------------------------------------------------
-- Notation  -------------------------------------------------------------------
--------------------------------------------------------------------------------

namespace SciLean.Notation


syntax "∂> " term:66 : term
syntax "∂> " diffBinder ", " term:66 : term
syntax "∂> " "(" diffBinder ")" ", " term:66 : term

syntax "∂>! " term:66 : term
syntax "∂>! " diffBinder ", " term:66 : term
syntax "∂>! " "(" diffBinder ")" ", " term:66 : term

open Lean Elab Term Meta in
elab_rules : term
| `(∂> $f $x $xs*) => do
  let X ← inferType (← elabTerm x none)
  let sX ← exprToSyntax X
  elabTerm (← `(fwdFDeriv (X:=$sX) defaultScalar% $f $x $xs*)) none

| `(∂> $f) => do
  elabTerm (← `(fwdFDeriv defaultScalar% $f)) none


macro_rules
| `(∂> $x:term, $b) => `(∂> (fun $x => $b))
| `(∂> $x:term := $val:term, $b) => `(∂> (fun $x => $b) $val)
| `(∂> $x:term : $type:term, $b) => `(∂> fun $x : $type => $b)
| `(∂> $x:term := $val:term ; $dir:term, $b) => `(∂> (fun $x => $b) $val $dir)
-- with brackets
| `(∂> ($x:term := $val:term), $b) => `(∂> (fun $x => $b) $val)
| `(∂> ($x:term := $val:term; $dir:term), $b) => `(∂> (fun $x => $b) $val $dir)


macro_rules
| `(∂>! $f $xs*) => `((∂> $f $xs*) rewrite_by autodiff; autodiff; autodiff)
| `(∂>! $f) => `((∂> $f) rewrite_by autodiff; autodiff; autodiff)
| `(∂>! $x:term, $b) => `(∂>! (fun $x => $b))
| `(∂>! $x:term := $val:term, $b) => `(∂>! (fun $x => $b) $val)
| `(∂>! $x:term : $type:term, $b) => `(∂>! fun $x : $type => $b)
| `(∂>! $x:term := $val:term ; $dir:term, $b) => `(∂>! (fun $x => $b) $val $dir)
-- with brackets
| `(∂>! ($x:term := $val:term), $b) => `(∂>! (fun $x => $b) $val)
| `(∂>! ($x:term := $val:term; $dir:term), $b) => `(∂>! (fun $x => $b) $val $dir)


@[app_unexpander fwdFDeriv] def unexpandfwdFDeriv : Lean.PrettyPrinter.Unexpander

  | `($(_) $_ $f:term $x $dx) =>
    match f with
    | `(fun $x':ident => $b:term) => `(∂> ($x':ident:=$x;$dx), $b)
    | `(fun ($x':ident : $_) => $b:term) => `(∂> ($x':ident:=$x;$dx), $b)
    | _  => `(∂> $f:term $x $dx)

  | `($(_) $_ $f:term $x) =>
    match f with
    | `(fun $x':ident => $b:term) => `(∂> ($x':ident:=$x), $b)
    | `(fun ($x':ident : $_) => $b:term) => `(∂> ($x':ident:=$x), $b)
    | _  => `(∂> $f:term $x)

  | `($(_) $_ $f:term) =>
    match f with
    | `(fun $x':ident => $b:term) => `(∂> $x':ident, $b)
    | `(fun ($x':ident : $ty) => $b:term) => `(∂> ($x' : $ty), $b)
    | _  => `(∂> $f)

  | _  => throw ()
