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
    `(doElem| $x:ident := modifyElem ($x:ident) $i $g)
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
macro "⊞ " x:term " => " b:term:51 : term => `(introElemNotation fun $x => $b)
macro "⊞ " x:term " : " X:term " => " b:term:51 : term => `(introElemNotation fun ($x : $X) => $b)

@[app_unexpander introElemNotation] 
def unexpandIntroElemNotation : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:term => $b) => 
    `(⊞ $x:term => $b)
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

namespace ArrayType.PowerNotation

class SHPow {α : Sort u} {β : Sort v} {γ : outParam (Sort w)} (a :α) (b : β) (c : outParam γ)
def SHPow.pow {α β γ} (a : α) (b : β) {c : γ} [SHPow a b c] := c

instance {Cont Idx Elem} [ArrayTypeNotation Cont Idx Elem] : SHPow Elem Idx (arrayTypeCont Idx Elem)  := ⟨⟩
instance {α β γ} (x : α) (y : β) [HPow α β γ] : SHPow x y (HPow.hPow x y):= ⟨⟩
open Lean Elab Term Meta in
elab:40 (priority:=high) x:term:41 " ^ " y:term:42 : term => withFreshMacroScope do
  let x ← elabTerm (← `(SHPow.pow $x $y)) none
  return x.getArg! 5

/- #check K ^ (κ×ι)
#eval 2 ^ 3

 -/

/- open Lean Elab Term in
elab:40 (priority:=high) x:term:41 " ^ " y:term:42 : term =>
  try 
    let y ← elabTerm y none
    let x ← elabTerm x none
    let z ← Meta.mkAppOptM ``arrayTypeCont #[y,x,none,none]
    return z
  catch _ => do
    return ← elabTerm (← `(HPow.hPow $x $y)) none
 -/
@[app_unexpander arrayTypeCont] def unexpandArrayTypeCont : Lean.PrettyPrinter.Unexpander
  | `($(_) $I $X) => 
    `($X ^ $I)
  | _  => throw ()


-- Notation: Float^[10,20] --
-----------------------------

declare_syntax_cat dimSpec
syntax term : dimSpec
syntax (priority:=high) "[" dimSpec,+ "]" : dimSpec
syntax "[" term ":" term "]": dimSpec

/-- `x^[y]` is either array type or iterated function depending on the type of `x`.

**iterated function** `f^[n]` call `f` n-times e.g. `f^[3] = f∘f∘f`

**type product** `Float^[n]` array of n elemts with values in `Float`

The array notation is quite flexible and allows you to create arrays indexed with various types. 
Examples where `n m k l : USize`, `a b : Int64` and `ι κ : Type` are types with `Index _` instance:
- `Float^[n]` index type: `Idx n` i.e. numbers `0,...,n-1`
- `Float^[n,m]` index type: `Idx n × Idx m` i.e. paris `(0,0),(0,1),...,(1,0),(1,1),...,(n-1,m-1)`
- `Float^[[-a:b]]` index type :`Idx' (-a) b` i.e. closed interval from `-a` to `b` (`={-a, -a+1, ..., b-1, b}`)
- `Float^[k,l,m]` index type: `Idx k × Idx l × Idx m` - type product is right associated by default
- `Float^[[k,l],m]` index type: `(Idx k × Idx l) × Idx m`  - left associated product requires explicit brackets
- `Float^[ι]` index type `ι` - generic type with `Index ι` instances
- `Float^[ι,[10,[-a:b]],κ]` index type: `ι × (Idx 10 × Idx' (-a) b) × κ` - mix of all above
-/
syntax (name:=typeIntPower) (priority:=high) term "^[" dimSpec,* "]" : term 

open Lean Meta Elab Term Qq
partial def expand' (l : List (TSyntax `dimSpec)) : TermElabM Expr := 
  match l with
  | []  => default
  | [t] => 
    match t with
    | `(dimSpec| $n:term) => do
      try 
        let n ← elabTerm n q(USize)
        return ← mkAppM ``Idx #[n]
      catch _ =>
        return ← elabTerm n none
    | `(dimSpec| [$n:term : $m:term]) => do elabTerm (← `(Idx' $n $m)) none
    | `(dimSpec| [$ds:dimSpec,*]) => expand' ds.getElems.toList
    | _ => throwError "unexpected type power syntax"
  | t :: l' =>  do
    let a ← expand' [t]
    let b ← expand' l'
    mkAppM ``Prod #[a,b]


open Lean Meta Elab Term  
elab_rules (kind:=typeIntPower) : term
| `($x:term ^[$ns,*]) => do
  let X ← elabTerm x none

  if ¬(← isType (← inferType X)) then
    if ns.getElems.size != 1 then
      throwUnsupportedSyntax
    else
      match ns.getElems[0]! with
      | `(dimSpec| $n:term) => 
        let f ← elabTerm x none
        let n ← elabTerm n q(Nat)
        return ← mkAppM ``Nat.iterate #[f,n]
      | _ => throwUnsupportedSyntax

  let Y ← expand' ns.getElems.toList  
  let C ← mkFreshTypeMVar
  let inst ← synthInstance <| mkAppN (← mkConst ``ArrayTypeNotation) #[C,Y,X]
  let C ← whnfR (← instantiateMVars C)
  return ← instantiateMVars <| ← mkAppOptM ``arrayTypeCont #[Y,X,C,inst]

end ArrayType.PowerNotation

