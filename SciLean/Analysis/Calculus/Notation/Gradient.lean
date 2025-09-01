import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.AD.HasVecFwdFDeriv
import SciLean.Analysis.Calculus.Notation.Deriv

namespace SciLean.Notation

syntax (name:=gradNotation1) "∇ " term:66 : term
syntax "∇ " diffBinder ", " term:66 : term
syntax "∇ " "(" diffBinder ")" ", " term:66 : term

syntax "∇! " term:66 : term
syntax "∇! " diffBinder ", " term:66 : term
syntax "∇! " "(" diffBinder ")" ", " term:66 : term


open Lean Elab Term Meta in
elab_rules (kind:=gradNotation1) : term
| `(∇ $f $x $xs*) => do
  elabTerm (← `(jacobianMat defaultScalar% $f $x $xs*)) none

  -- let K ← elabTerm (← `(defaultScalar%)) none
  -- let X ← inferType (← elabTerm x none)
  -- let Y ← mkFreshTypeMVar
  -- let XY ← mkArrow X Y
  -- -- Y might also be infered by the function `f`
  -- let fExpr ← withoutPostponing <| elabTermEnsuringType f XY false
  -- let .some (_,Y) := (← inferType fExpr).arrow?
  --   | return ← throwUnsupportedSyntax
  -- let sX ← exprToSyntax X
  -- let sK ← exprToSyntax K
  -- let sY ← exprToSyntax Y
  -- if (← isDefEq K Y) then
  --   elabTerm (← `(fgradient (X:=$sX) (K:=$sK) $f $x $xs*)) none false
  -- else
  --   elabTerm (← `(adjointFDeriv (X:=$sX) (Y:=$sY) defaultScalar% $f $x $xs*)) none false

| `(∇ $f) => do
  elabTerm (← `(jacobianMat defaultScalar% $f)) none

  -- let K ← elabTerm (← `(defaultScalar%)) none
  -- let X ← mkFreshTypeMVar
  -- let Y ← mkFreshTypeMVar
  -- let XY ← mkArrow X Y
  -- let fExpr ← withoutPostponing <| elabTermEnsuringType f XY false
  -- if let .some (_,Y) := (← inferType fExpr).arrow? then
  --   if (← isDefEq K Y) then
  --     elabTerm (← `(fgradient $f)) none false
  --   else
  --     elabTerm (← `(adjointFDeriv defaultScalar% $f)) none false
  -- else
  --   throwUnsupportedSyntax

macro_rules
| `(∇ $x:term, $f)              => `(∇ fun $x => $f)
| `(∇ $x:term : $type:term, $f) => `(∇ fun $x : $type => $f)
| `(∇ $x:term := $val:term, $f) => `(∇ (fun $x => $f) $val)
-- with brackets
| `(∇ ($x:term := $val:term), $f) => `(∇ (fun $x => $f) $val)

macro_rules
| `(∇! $f)                       => `((∇ $f) rewrite_by autodiff)
| `(∇! $x:term, $f)              => `(∇! fun $x => $f)
| `(∇! $x:term : $type:term, $f) => `(∇! fun $x : $type => $f)
| `(∇! $x:term := $val:term, $f) => `((∇ (fun $x => $f) $val) rewrite_by autodiff)
-- with brackets
| `(∇! ($x:term := $val:term), $f) => `(∇! (fun $x => $f) $val)

@[app_unexpander jacobianMat] def unexpandGradient : Lean.PrettyPrinter.Unexpander

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

-- @[app_unexpander fgradient] def unexpandScalarGradient : Lean.PrettyPrinter.Unexpander

--   | `($(_) $f:term $x $y $ys*) =>
--     match f with
--     | `(fun $x':ident => $b:term) => `((∇ $x':ident:=$x, $b) $y $ys*)
--     | _  => `(∇ $f:term $x:term $y $ys*)

--   | `($(_) $f:term $x) =>
--     match f with
--     | `(fun $x':ident => $b:term) => `(∇ ($x':ident:=$x), $b)
--     | `(fun ($x':ident : $_) => $b:term) => `(∇ ($x':ident:=$x), $b)
--     | _  => `(∇ $f:term $x)

--   | `($(_) $f:term) =>
--     match f with
--     | `(fun $x':ident => $b:term) => `(∇ $x':ident, $b)
--     | `(fun ($x':ident : $ty) => $b:term) => `(∇ ($x' : $ty), $b)
--     | _  => `(∇ $f)

--   | _  => throw ()
