import SciLean.Data.ArrayType.Basic

namespace SciLean


open Lean Parser 
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
    `(doElem| $x:ident := ArrayType.modifyElem ($x:ident) $i $g)
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



section ArrayTypeNotation

open Lean

-- syntax myFunBinder := " ( " ident  " : " term ("⇒" term)? " )"

-- syntax (priority:=high)  --(name:=lambdaParserWithArrayType) 
--   " λ " myFunBinder* " => " term : term

-- macro_rules -- (kind := lambdaParserWithArrayType) 
-- | `(λ ($x:ident : $X:term) => $b) => `(fun ($x : $X:term) => $b)
-- | `(λ ($f:ident : $X:term ⇒ $Y:term) => $b) =>
--   let XY := mkIdent s!"{X.raw.prettyPrint}⇒{Y.raw.prettyPrint}"
--   `(fun {$XY : Type} [ArrayType $XY $X $Y] ($f : $XY) => $b)
-- | `(λ $x:myFunBinder $xs:myFunBinder* => $b) =>
--   `(λ $x:myFunBinder => λ $xs:myFunBinder* => $b)


-- syntax vecType := " Vec "

-- syntax arrayType := term " ⇒ " term
-- syntax myExplicitFunBinder := " *( " ident  " : " arrayType  " )"
-- syntax myFunBinder := Parser.Term.funBinder <|> myExplicitFunBinder 

-- syntax (priority:=low)
--   " λ " myFunBinder* " => " term : term

-- macro_rules 
-- | `(λ *($f:ident : $X:term ⇒ $Y:term) $xs:myFunBinder* => $b) =>
--   let XY := mkIdent s!"{X.raw.prettyPrint}⇒{Y.raw.prettyPrint}"
--   if xs.size = 0 then
--     `(fun {$XY : Type} [ArrayType $XY $X $Y] ($f : $XY) => $b)
--   else
--     `(fun {$XY : Type} [ArrayType $XY $X $Y] ($f : $XY) => λ $xs* => $b)
-- -- | `(λ $x:myFunBinder $xs:myFunBinder* => $b) =>
-- --   `(λ $x:myFunBinder => λ $xs:myFunBinder* => $b)
-- -- | `(λ $x:funBinder => $b) => `(fun $x => $b)

-- #check λ (f : Nat ⇒ Float) (i : Nat) => f[i]
#check λ (f : Nat → Float) (i) => f i
#check λ (f : Nat → Float) i => f i

end ArrayTypeNotation

-- This should be improved such that we can specify the type of arguments
-- This clashes with typeclass arguments, but who in their right mind
-- starts a lambda arguments with a typeclass?
-- syntax (name:=ArrayTypeIntroSyntax) "λ" "[" Lean.Parser.ident,+ "]" " ==> " term : term

-- macro_rules (kind := ArrayTypeIntroSyntax)
-- | `(λ [ $id1:ident ] ==> $b:term) => `(introElem λ $id1 => $b)
-- | `(λ [ $id1:ident, $id2:ident ] ==> $b:term) => `(introElem λ ($id1, $id2) => $b)
-- | `(λ [ $id1:ident, $id2:ident, $id3:ident ] ==> $b:term) => `(introElem λ ($id1, $id2, $id3) => $b)


-- syntax (name:=ArrayTypeIntroSyntax) "λ" funBinder+ " ==> " term : term


-- macro_rules (kind := ArrayTypeIntroSyntax)
-- | `(λ $xs:funBinder* ==> $b:term) => `(introElem λ $xs* => $b)
-- | `(λ [ $id1:ident, $id2:ident ] ==> $b:term) => `(introElem λ ($id1, $id2) => $b)
-- | `(λ [ $id1:ident, $id2:ident, $id3:ident ] ==> $b:term) => `(introElem λ ($id1, $id2, $id3) => $b)


-- variable {Cont} [ArrayType Cont (Fin 10) (Fin 10)]
-- #check ((λ i ==> (i : Fin 10)))

-- #check ((λ i ==> (i : Fin 10)))


