import SciLean.Data.ArrayType.Basic
import SciLean.Data.ListN
import Batteries.Lean.Expr
import Qq


namespace SciLean

open Lean Parser
open TSyntax.Compat
open LeanColls

abbrev typeOf {α} (_ : α) := α

class ArrayTypeNotation (Cont : outParam $ Type _) (Idx Elem : Type _)

abbrev arrayTypeCont (Idx Elem) {Cont : outParam $ Type _} [ArrayTypeNotation Cont Idx Elem] := Cont


-- Notation: ⊞ i => f i --
--------------------------

abbrev introElemNotation {Cont Idx Elem} [DecidableEq Idx] [ArrayType Cont Idx Elem] [ArrayTypeNotation Cont Idx Elem]
  (f : Idx → Elem)
  : Cont
  := Indexed.ofFn (C := arrayTypeCont Idx Elem) f

open Lean.TSyntax.Compat in
-- macro "⊞ " x:term " => " b:term:51 : term => `(introElemNotation fun $x => $b)
-- macro "⊞ " x:term " : " X:term " => " b:term:51 : term => `(introElemNotation fun ($x : $X) => $b)

-- The `by exact` is a hack to make certain case work
--    see: https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/uncurry.20fails.20with.20.60Icc.60
open Term Function Lean Elab Term Meta in
elab "⊞ " xs:funBinder* " => " b:term:51 : term  => do
  let fn ← elabTerm (← `(fun $xs* => $b)) none
  let arity := (← inferType fn).forallArity

  try
    -- uncurry if necessary
    let fn ←
      if arity = 1 then
        pure fn
      else
        mkAppM ``HasUncurry.uncurry #[fn]

    let .some (Idx, Elem) := (← inferType fn).arrow?
      | throwError "⊞ _ => _: expectes function type {← ppExpr (← inferType fn)}"

    let Cont ← mkAppOptM ``arrayTypeCont #[Idx, Elem, none, none]
    let Cont := Cont.getRevArg! 1

    mkAppOptM ``Indexed.ofFn #[Cont, Idx, Elem, none, fn]
  catch _ =>
    if arity = 1 then
      elabTerm (← `(Indexed.ofFn fun $xs* => $b)) none
    else if arity = 2 then
      elabTerm (← `(Indexed.ofFn (Function.uncurry fun $xs* => $b))) none
    else
      throwError "notation `⊞ _ => _` is not supported for high rank arrays when types are unknown\
                  \nplease specify the types!"


-- variable {Cont Idx Elem} [ArrayType Cont Idx Elem] [ArrayTypeNotation Cont Idx Elem] (e : Elem) (c : Cont)

-- set_option pp.funBinderTypes true in
-- example : c = ⊞ (_ : Idx) => e := sorry




@[app_unexpander introElemNotation]
def unexpandIntroElemNotation : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x => $b) =>
    `(⊞ $x:term => $b)
  | _  => throw ()


-- Notation: ⊞[1,2,3] --
------------------------

/-- A notation for creating a `DataArray` from a list of elements. -/
syntax (name := dataArrayNotation) (priority:=high)
  "⊞[" ppRealGroup(sepBy1(ppGroup(term,+,?), ";", "; ", allowTrailingSep)) "]" : term


open Lean Qq Elab Term in
/-- Elaborate a `⊞[...]` notation into a `Indexed.ofFn` term. -/
elab_rules (kind := dataArrayNotation) : term
  | `(⊞[$[$[$rows],*];*]) => do
    let m := rows.size
    let n := if h : 0 < m then rows[0].size else 0
    let elems := rows.flatten

    -- check dimenstions
    for row in rows do
      if row.size ≠ n then
        throwErrorAt (mkNullNode row) s!"\
          Rows must be of equal length; this row has {row.size} items, \
          the previous rows have {n}"

    let n := Syntax.mkNumLit (toString n)
    let m := Syntax.mkNumLit (toString rows.size)

    let Idx ←
      if rows.size = 1 then
        `(Fin $n)
      else
        `(Fin $m × Fin $n)

    let dataArray := mkIdent `DataArrayN
    let fn ←
      elabTerm (←`(@Indexed.ofFn.{_,_,_,0} ($dataArray _ _) _ _ _
                    fun (i : $Idx) => [$elems,*].get! (IndexType.toFin.{_,0} i))) none

    return fn


/-- Unexpander for `⊞[...]` and `⊞ i => ...` notation.

TODO: support matrix literals -/
@[app_unexpander LeanColls.Indexed.ofFn] def unexpandIndexedOfFn : Lean.PrettyPrinter.Unexpander
  | `($(_) $f) =>
    match f with
    | `(fun $_ => List.get! [$xs,*] $_) =>
      `(⊞[$xs,*])
    | `(fun $i => $b) =>
      `(⊞ $i => $b)
    | _ =>
      throw ()
  | _ => throw ()



-- Notation: Float ^ Idx n --
-----------------------------

namespace ArrayType.PowerNotation

-- class SHPow {α : Sort u} {β : Sort v} {γ : outParam (Sort w)} (a :α) (b : β) (c : outParam γ)
-- def SHPow.pow {α β γ} (a : α) (b : β) {c : γ} [SHPow a b c] := c

-- instance {Cont Idx Elem} [ArrayTypeNotation Cont Idx Elem] : SHPow Elem Idx (arrayTypeCont Idx Elem)  := ⟨⟩
-- instance {α β γ} (x : α) (y : β) [HPow α β γ] : SHPow x y (HPow.hPow x y):= ⟨⟩
-- open Lean Elab Term Meta in
-- elab:40 (priority:=high) x:term:41 " ^ " y:term:42 : term => withFreshMacroScope do
--   let x ← elabTerm (← `(SHPow.pow $x $y)) none
--   return x.getArg! 5

-- /- #check K ^ (κ×ι)
-- #eval 2 ^ 3

--  -/

-- /- open Lean Elab Term in
-- elab:40 (priority:=high) x:term:41 " ^ " y:term:42 : term =>
--   try
--     let y ← elabTerm y none
--     let x ← elabTerm x none
--     let z ← Meta.mkAppOptM ``arrayTypeCont #[y,x,none,none]
--     return z
--   catch _ => do
--     return ← elabTerm (← `(HPow.hPow $x $y)) none
--  -/
-- @[app_unexpander arrayTypeCont] def unexpandArrayTypeCont : Lean.PrettyPrinter.Unexpander
--   | `($(_) $I $X) =>
--     `($X ^ $I)
--   | _  => throw ()


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
        let n ← elabTerm n q(Nat)
        return ← mkAppM ``Fin #[n]
      catch _ =>
        return ← elabTerm n none
    | `(dimSpec| [$n:term : $m:term]) => do elabTerm (← `(↑(Set.Icc ($n : Int) ($m : Int)))) q(Type)
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
  let inst ← synthInstance <| mkAppN (← mkConstWithFreshMVarLevels ``ArrayTypeNotation) #[C,Y,X]
  let C ← whnfR (← instantiateMVars C)
  let result ← instantiateMVars <| ← mkAppOptM ``arrayTypeCont #[Y,X,C,inst]
  return result.getRevArg! 1

end ArrayType.PowerNotation
