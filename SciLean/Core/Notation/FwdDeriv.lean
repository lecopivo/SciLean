import SciLean.Core.FunctionTransformations.FwdDeriv
import SciLean.Core.Notation.CDeriv


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
  elabTerm (← `(fwdDeriv defaultScalar% $f $x $xs*)) none

| `(∂> $f) => do
  elabTerm (← `(fwdDeriv defaultScalar% $f)) none


macro_rules
| `(∂> $x:ident, $b) => `(∂> (fun $x => $b))
| `(∂> $x:ident := $val:term, $b) => `(∂> (fun $x => $b) $val)
| `(∂> $x:ident : $type:term, $b) => `(∂> fun $x : $type => $b)
| `(∂> $x:ident := $val:term ; $dir:term, $b) => `(∂> (fun $x => $b) $val $dir)
| `(∂> ($b:diffBinder), $f)       => `(∂> $b, $f)


macro_rules
| `(∂>! $f $xs*) => `((∂> $f $xs*) rewrite_by autodiff; autodiff; autodiff)
| `(∂>! $f) => `((∂> $f) rewrite_by autodiff; autodiff; autodiff)
| `(∂>! $x:ident, $b) => `(∂>! (fun $x => $b))
| `(∂>! $x:ident := $val:term, $b) => `(∂>! (fun $x => $b) $val)
| `(∂>! $x:ident : $type:term, $b) => `(∂>! fun $x : $type => $b)
| `(∂>! $x:ident := $val:term ; $dir:term, $b) => `(∂>! (fun $x => $b) $val $dir)
| `(∂>! ($b:diffBinder), $f)       => `(∂>! $b, $f)


@[app_unexpander fwdDeriv] def unexpandFwdDeriv : Lean.PrettyPrinter.Unexpander

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
