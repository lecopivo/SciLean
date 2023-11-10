import SciLean.Data.ArrayType.Basic
import SciLean.Data.ListN
import Qq
namespace SciLean

open Lean Parser 
open TSyntax.Compat


abbrev typeOf {α} (_ : α) := α

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

class ArrayTypeNotation (Cont : outParam $ Type _) (Idx Elem : Type _)

abbrev arrayTypeCont (Idx Elem) {Cont : outParam $ Type _} [ArrayTypeNotation Cont Idx Elem] := Cont


-- Notation: ⊞ i => f i --
--------------------------

abbrev introElemNotation {Cont Idx Elem} [ArrayType Cont Idx Elem] [ArrayTypeNotation Cont Idx Elem]  
  (f : Idx → Elem)
  : Cont 
  := introElem (Cont := arrayTypeCont Idx Elem) f

open Lean.TSyntax.Compat in
macro "⊞ " xs:Lean.explicitBinders " => " b:term:51 : term => Lean.expandExplicitBinders ``introElemNotation xs b

@[app_unexpander introElemNotation] 
def unexpandIntroElemNotation : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => $b) => 
    `(⊞ $x:ident => $b)
  | _  => throw ()


-- Notation: ⊞[1,2,3] --
------------------------


syntax (name:=arrayTypeLiteral) " ⊞[" term,* "] " : term

open Lean Meta Elab Term Qq
macro_rules 
 | `(⊞[ $x:term, $xs:term,* ]) => do 
   let n := Syntax.mkNumLit (toString (xs.getElems.size + 1))   
   `(ListN.toArrayType (arrayTypeCont (Idx ($n).toUSize) (typeOf $x)) [$x,$xs,*]')
  -- let n := Syntax.mkNumLit (toString xs.getElems.size)
  -- `(term| ListN.toArrayType (arrayType #[$xs,*] $n (by rfl))

@[app_unexpander Array.toArrayType] 
def unexpandArrayToArrayType : Lean.PrettyPrinter.Unexpander
  | `($(_) #[$ys,*] $_*) =>     
    `(⊞[$ys,*])
  | _  => throw ()

-- variable {CC : USize → Type} [∀ n, ArrayType (CC n) (Idx n) Float] [∀ n, ArrayTypeNotation (CC n) (Idx n) Float]
-- #check [1.0,2.0,3.0]'.toArrayType (CC 3)
-- #check ⊞[1.0,2.0,3.0]


-- Notation: Float ^ Idx n --
-----------------------------

open Lean Elab Term in
elab:40 (priority:=high) x:term:41 " ^ " y:term:42 : term =>
  try 
    let y ← elabTerm y none
    let x ← elabTerm x none
    let z ← Meta.mkAppOptM ``arrayTypeCont #[y,x,none,none]
    return z
  catch _ => do
    return ← elabTerm (← `(HPow.hPow $x $y)) none

@[app_unexpander arrayTypeCont] def unexpandArrayTypeCont : Lean.PrettyPrinter.Unexpander
  | `($(_) $I $X) => 
    `($X ^ $I)
  | _  => throw ()
