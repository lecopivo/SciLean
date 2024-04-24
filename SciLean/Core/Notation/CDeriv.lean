import SciLean.Core.FunctionTransformations.CDeriv
import SciLean.Tactic.Autodiff

--------------------------------------------------------------------------------
-- Notation  -------------------------------------------------------------------
--------------------------------------------------------------------------------

namespace SciLean.Notation

syntax diffBinderType  := " : " term
syntax diffBinderValue := ":=" term (";" term)?
syntax diffBinder := term (diffBinderType <|> diffBinderValue)?

syntax "∂ " term:66 : term
syntax "∂ " diffBinder ", " term:66 : term
syntax "∂ " "(" diffBinder ")" ", " term:66 : term

syntax "∂! " term:66 : term
syntax "∂! " diffBinder ", " term:66 : term
syntax "∂! " "(" diffBinder ")" ", " term:66 : term

open Lean Elab Term Meta in
elab_rules : term
| `(∂ $f $x $xs*) => do
  let K ← elabTerm (← `(defaultScalar%)) none
  let X ← inferType (← elabTerm x none)
  let Y ← mkFreshTypeMVar
  let XY ← mkArrow X Y
  -- X might also be infered by the function `f`
  let fExpr ← withoutPostponing <| elabTermEnsuringType f XY false
  let .some (X,_) := (← inferType fExpr).arrow? | return ← throwUnsupportedSyntax
  if (← isDefEq K X) && xs.size = 0 then
    elabTerm (← `(scalarCDeriv defaultScalar% $f $x $xs*)) none false
  else
    elabTerm (← `(cderiv defaultScalar% $f $x $xs*)) none false

| `(∂ $f) => do
  let K ← elabTerm (← `(defaultScalar%)) none
  let X ← mkFreshTypeMVar
  let Y ← mkFreshTypeMVar
  let XY ← mkArrow X Y
  let fExpr ← withoutPostponing <| elabTermEnsuringType f XY false
  if let .some (X,_) := (← inferType fExpr).arrow? then
    if (← isDefEq K X) then
      elabTerm (← `(scalarCDeriv defaultScalar% $f)) none false
    else
      elabTerm (← `(cderiv defaultScalar% $f)) none false
  else
    throwUnsupportedSyntax

-- in this case we do not want to call scalarCDeriv
| `(∂ $x:ident := $val:term ; $dir:term, $b) => do
  elabTerm (← `(cderiv defaultScalar% (fun $x => $b) $val $dir)) none


macro_rules
| `(∂ $x:ident, $b) => `(∂ (fun $x => $b))
| `(∂ $x:ident := $val:term, $b) => `(∂ (fun $x => $b) $val)
| `(∂ $x:ident : $type:term, $b) => `(∂ fun $x : $type => $b)
| `(∂ ($b:diffBinder), $f)       => `(∂ $b, $f)

macro_rules
-- in some cases it is still necessary to call fun_trans multiple times
-- | `(∂! $f $xs*) => `((∂ $f $xs*) rewrite_by fun_trans; fun_trans; fun_trans)
| `(∂! $f) => `((∂ $f) rewrite_by (try unfold scalarCDeriv); autodiff; autodiff)
| `(∂! $x:ident, $b) => `(∂! (fun $x => $b))
| `(∂! $x:ident := $val:term, $b) => `(∂! (fun $x => $b) $val)
| `(∂! $x:ident := $val:term;$dir:term, $b) => `(((∂ $x:term:=$val;$dir, $b) rewrite_by (try unfold scalarCDeriv);fun_trans))
| `(∂! $x:ident : $type:term, $b) => `(∂! fun $x : $type => $b)
| `(∂! ($b:diffBinder), $f)       => `(∂! $b, $f)


@[app_unexpander cderiv] def unexpandCDeriv : Lean.PrettyPrinter.Unexpander

  | `($(_) $_ $f:term $x $dx $y $ys*) =>
    match f with
    | `(fun $x':ident => $b:term) => `((∂ $x':ident:=$x;$dx, $b) $y $ys*)
    | _  => `(∂ $f:term $x:term $dx $y $ys*)


  | `($(_) $K $f:term $x $dx) =>
    match f with
    | `(fun $x':ident => $b:term) => `(∂ ($x':ident:=$x;$dx), $b)
    | `(fun ($x':ident : $_) => $b:term) => `(∂ ($x':ident:=$x;$dx), $b)
    | _  => `(∂ $f:term $x $dx)

  | `($(_) $K $f:term $x) =>
    match f with
    | `(fun $x':ident => $b:term) => `(∂ ($x':ident:=$x), $b)
    | `(fun ($x':ident : $_) => $b:term) => `(∂ ($x':ident:=$x), $b)
    | _  => `(∂ $f:term $x)

  | `($(_) $K $f:term) =>
    match f with
    | `(fun $x':ident => $b:term) => `(∂ $x':ident, $b)
    | `(fun ($x':ident : $ty) => $b:term) => `(∂ ($x' : $ty), $b)
    | _  => `(∂ $f)

  | _  => throw ()

@[app_unexpander scalarCDeriv] def unexpandScalarCDeriv : Lean.PrettyPrinter.Unexpander

  | `($(_) $_ $f:term $x $y $ys*) =>
    match f with
    | `(fun $x':ident => $b:term) => `((∂ $x':ident:=$x, $b) $y $ys*)
    | _  => `(∂ $f:term $x:term $y $ys*)


  | `($(_) $K $f:term $x) =>
    match f with
    | `(fun $x':ident => $b:term) => `(∂ ($x':ident:=$x), $b)
    | `(fun ($x':ident : $_) => $b:term) => `(∂ ($x':ident:=$x), $b)
    | _  => `(∂ $f:term $x)

  | `($(_) $K $f:term) =>
    match f with
    | `(fun $x':ident => $b:term) => `(∂ $x':ident, $b)
    | `(fun ($x':ident : $ty) => $b:term) => `(∂ ($x' : $ty), $b)
    | _  => `(∂ $f)

  | _  => throw ()
