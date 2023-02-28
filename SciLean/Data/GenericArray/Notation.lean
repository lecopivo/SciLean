import SciLean.Data.GenericArray.Basic

namespace SciLean


open Lean Parser Term
open TSyntax.Compat



syntax (priority := high) atomic(Lean.Parser.Term.ident) noWs "[" term "]" " := " term : doElem
macro_rules
| `(doElem| $x:ident[ $i:term ] := $xi) => do
  let lhs ← `($x[$i])
  -- Do we alias? Does `x[i]` appear on the right hand side too?
  -- For example `x[i] := 2 * x[i]`
  -- In such cases we want to use `modifyElem` instead of `setElem`
  if let .some _ := xi.raw.find? (λ x => lhs.raw == x) then
    let var ← `(y)
    let xi' ← xi.raw.replaceM (λ s => if s == lhs.raw then pure $ .some var else pure $ none)
    let g ← `(λ ($var : typeOf $lhs) => $xi')
    `(doElem| $x:ident := GenericArray.modifyElem ($x:ident) $i $g)
  else 
    `(doElem| $x:ident := setElem ($x:ident) $i $xi)

--- Syntax for: x[i] := y, x[i] ← y, x[i] += y, x[i] -= y, x[i] *= y
syntax (priority := high) atomic(Lean.Parser.Term.ident) noWs "[" term "]" " ← " term : doElem
syntax atomic(Term.ident) noWs "[" term "]" " += " term : doElem
syntax atomic(Term.ident) noWs "[" term "]" " +.= " term : doElem
syntax atomic(Term.ident) noWs "[" term "]" " -= " term : doElem
/-- Multiplication from right -/
syntax atomic(Term.ident) noWs "[" term "]" " *= " term : doElem
/-- Multiplication from left -/
syntax atomic(Term.ident) noWs "[" term "]" " *.= " term : doElem
syntax atomic(Term.ident) noWs "[" term "]" " /= " term : doElem

--- Rules for: x[i] := y, x[i] += y, x[i] -= y, x[i] *= y
macro_rules
| `(doElem| $x:ident[ $i:term ] ← $xi) => `(doElem| $x:ident := setElem ($x:ident) $i (← $xi))
macro_rules
| `(doElem| $x:ident[ $i:term ] += $xi) => `(doElem| $x:ident[$i] := $x[$i] + $xi)
macro_rules
| `(doElem| $x:ident[ $i:term ] +.= $xi) => `(doElem| $x:ident[$i] := $xi + $x[$i])
macro_rules
| `(doElem| $x:ident[ $i:term ] -= $xi) => `(doElem| $x:ident[$i] := $x[$i] - $xi)
macro_rules
| `(doElem| $x:ident[ $i:term ] *= $xi) => `(doElem| $x:ident[$i] := $x[$i] * $xi)
macro_rules
| `(doElem| $x:ident[ $i:term ] -= $xi) => `(doElem| $x:ident[$i] := $xi * $x[$i])
macro_rules
| `(doElem| $x:ident[ $i:term ] -= $xi) => `(doElem| $x:ident[$i] := $x[$i] / $xi)

-- This should be improved such that we can specify the type of arguments
-- This clashes with typeclass arguments, but who in their right mind
-- starts a lambda arguments with a typeclass?
-- syntax (name:=genericArrayIntroSyntax) "λ" "[" Lean.Parser.ident,+ "]" " ==> " term : term

-- macro_rules (kind := genericArrayIntroSyntax)
-- | `(λ [ $id1:ident ] ==> $b:term) => `(introElem λ $id1 => $b)
-- | `(λ [ $id1:ident, $id2:ident ] ==> $b:term) => `(introElem λ ($id1, $id2) => $b)
-- | `(λ [ $id1:ident, $id2:ident, $id3:ident ] ==> $b:term) => `(introElem λ ($id1, $id2, $id3) => $b)


-- syntax (name:=genericArrayIntroSyntax) "λ" funBinder+ " ==> " term : term


-- macro_rules (kind := genericArrayIntroSyntax)
-- | `(λ $xs:funBinder* ==> $b:term) => `(introElem λ $xs* => $b)
-- | `(λ [ $id1:ident, $id2:ident ] ==> $b:term) => `(introElem λ ($id1, $id2) => $b)
-- | `(λ [ $id1:ident, $id2:ident, $id3:ident ] ==> $b:term) => `(introElem λ ($id1, $id2, $id3) => $b)


-- variable {Cont} [GenericArray Cont (Fin 10) (Fin 10)]
-- #check ((λ i ==> (i : Fin 10)))

-- #check ((λ i ==> (i : Fin 10)))


