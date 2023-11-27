import SciLean.Core.FunctionTransformations.RevCDeriv
import SciLean.Core.Notation.Autodiff
import SciLean.Core.Notation.CDeriv


namespace SciLean.NotationOverField

scoped syntax (name:=gradNotation1) "∇ " term:66 : term
scoped syntax "∇ " diffBinder ", " term:66 : term
scoped syntax "∇ " "(" diffBinder ")" ", " term:66 : term
scoped syntax "∇! " term:66 : term
scoped syntax "∇! " diffBinder ", " term:66 : term
scoped syntax "∇! " "(" diffBinder ")" ", " term:66 : term


open Lean Elab Term Meta in
elab_rules (kind:=gradNotation1) : term
| `(∇ $f) => do
  let K := mkIdent (← currentFieldName.get)
  let KExpr ← elabTerm (← `($K)) none
  let fExpr ← elabTerm f none
  if let .some (_,Y) := (← inferType fExpr).arrow? then
    if (← isDefEq KExpr Y) then
      elabTerm (← `(scalarGradient $K $f)) none false
    else
      elabTerm (← `(gradient $K $f)) none false
  else
    throwUnsupportedSyntax

-- open Lean Elab Term Meta in
-- elab_rules (kind:=gradNotation1) : term
-- | `(∇ $x:ident := $val:term; $codir:term, $b) => do
--   let K := mkIdent (← currentFieldName.get)
--   elabTerm (← `(gradient $K (fun $x => $b) $val $codir)) none false

macro_rules
| `(∇ $x:ident, $f)              => `(∇ fun $x => $f)
| `(∇ $x:ident : $type:term, $f) => `(∇ fun $x : $type => $f)
| `(∇ $x:ident := $val:term, $f) => `((∇ fun $x => $f) $val)
| `(∇ ($b:diffBinder), $f)       => `(∇ $b, $f)
| `(∇! $f)                        => `((∇ $f) rewrite_by autodiff)
| `(∇! $x:ident, $f)              => `(∇! fun $x => $f)
| `(∇! $x:ident : $type:term, $f) => `(∇! fun $x : $type => $f)
| `(∇! $x:ident := $val:term, $f) => `((∇! fun $x => $f) $val)
| `(∇! ($b:diffBinder), $f)       => `(∇! $b, $f)


@[app_unexpander gradient] def unexpandGradient : Lean.PrettyPrinter.Unexpander

  | `($(_) $_ $f:term $x $dy $z $zs*) =>
    match f with
    | `(fun $x':ident => $b:term) => `((∇ $x':ident:=$x;$dy, $b) $z $zs*)
    | _  => `(∇ $f:term $x:term $dy $z $zs*)


  | `($(_) $K $f:term $x $dy) =>
    match f with
    | `(fun $x':ident => $b:term) => `(∇ ($x':ident:=$x;$dy), $b)
    | `(fun ($x':ident : $_) => $b:term) => `(∇ ($x':ident:=$x;$dy), $b)
    | _  => `(∇ $f:term $x $dy)

  | `($(_) $K $f:term $x) =>
    match f with
    | `(fun $x':ident => $b:term) => `(∇ ($x':ident:=$x), $b)
    | `(fun ($x':ident : $_) => $b:term) => `(∇ ($x':ident:=$x), $b)
    | _  => `(∇ $f:term $x)

  | `($(_) $K $f:term) =>
    match f with
    | `(fun $x':ident => $b:term) => `(∇ $x':ident, $b)
    | `(fun ($x':ident : $ty) => $b:term) => `(∇ ($x' : $ty), $b)
    | _  => `(∇ $f)

  | _  => throw ()

@[app_unexpander scalarGradient] def unexpandScalarGradient : Lean.PrettyPrinter.Unexpander

  | `($(_) $_ $f:term $x $y $ys*) =>
    match f with
    | `(fun $x':ident => $b:term) => `((∇ $x':ident:=$x, $b) $y $ys*)
    | _  => `(∇ $f:term $x:term $y $ys*)

  | `($(_) $K $f:term $x) =>
    match f with
    | `(fun $x':ident => $b:term) => `(∇ ($x':ident:=$x), $b)
    | `(fun ($x':ident : $_) => $b:term) => `(∇ ($x':ident:=$x), $b)
    | _  => `(∇ $f:term $x)

  | `($(_) $K $f:term) =>
    match f with
    | `(fun $x':ident => $b:term) => `(∇ $x':ident, $b)
    | `(fun ($x':ident : $ty) => $b:term) => `(∇ ($x' : $ty), $b)
    | _  => `(∇ $f)

  | _  => throw ()

end SciLean.NotationOverField
