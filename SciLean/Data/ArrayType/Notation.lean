import SciLean.Data.ArrayType.Basic
import SciLean.Data.ListN
import SciLean.Data.ArrayLike
import Batteries.Lean.Expr
import Qq


namespace SciLean

open Lean Parser
open TSyntax.Compat



-- Element access notation -------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


open Lean Elab Term Meta in
-- @[inherit_doc ArrayType.get]
elab:max (priority:=high+1) x:term noWs "[" i:term "]" : term => do
  try
    let x ← elabTerm x none
    let X ← inferType x
    let Idx ← mkFreshTypeMVar
    let cls := (mkAppN (← mkConstWithFreshMVarLevels ``DefaultIndex) #[X, Idx])
    let _ ← synthInstance cls
    let i ← elabTerm i Idx
    return ← mkAppOptM ``getElem #[X,Idx,none,none,x,i,Expr.const ``True.intro []]
  catch _ =>
    return ← elabTerm (← `(getElem $x $i (by get_elem_tactic))) none

/-- Turn an array of terms in into a tuple. -/
private def mkTuple (xs : Array (TSyntax `term)) : MacroM (TSyntax `term) :=
  `(term| ($(xs[0]!), $(xs[1:]),*))


/-- Element index can either be an index or a range. -/
syntax elemIndex := (term)? (":" (term)?)?

/--
The syntax `x[i,j,k]` gets the element of `x : X` indexed by `(i,j,k)`. It is required that there is
an instance `Indexed X I E` and `(i,j,k)` has type `I`.

This notation also support ranges, `x[:i,j₁:j₂,k]` returns a slice of `x`.

Note that product is right associated thus `x[i,j,k]`, `x[i,(j,k)]` and `x[(i,j,k)]` result in
the same expression.
-/
macro:max (name:=indexedGet) (priority:=high+1) x:term noWs "[" i:term ", " is:term,* "]" : term => do
  let idx ← mkTuple (#[i] ++ is.getElems)
  `($x[$idx])

-- todo: merge with `indexedGet`
--       right now I could not figure out how to correctly write down the corresponding macro_rules
@[inherit_doc indexedGet]
syntax:max (name:=indexedGetRanges) (priority:=high) term noWs "[" elemIndex "," elemIndex,* "]" : term


macro (priority:=high) x:ident noWs "[" ids:term,* "]" " := " xi:term : doElem => do
  let i ← mkTuple ids.getElems
  `(doElem| $x:ident := ArrayType.set $x $i $xi)

macro (priority:=high) x:ident noWs "[" ids:term,* "]" " ← " xi:term : doElem => do
  let i ← mkTuple ids.getElems
  `(doElem| $x:ident := ArrayType.set $x $i (← $xi))

macro x:ident noWs "[" ids:term,* "]" " += " xi:term : doElem => do
  let i ← mkTuple ids.getElems
  `(doElem| $x:ident := ArrayType.modify $x $i (fun xi => xi + $xi))

macro x:ident noWs "[" ids:term,* "]" " -= " xi:term : doElem => do
  let i ← mkTuple ids.getElems
  `(doElem| $x:ident := ArrayType.modify $x $i (fun xi => xi - $xi))

macro x:ident noWs "[" ids:term,* "]" " *= " xi:term : doElem => do
  let i ← mkTuple ids.getElems
  `(doElem| $x:ident := ArrayType.modify $x $i (fun xi => xi * $xi))

macro x:ident noWs "[" ids:term,* "]" " /= " xi:term : doElem => do
  let i ← mkTuple ids.getElems
  `(doElem| $x:ident := ArrayType.modify $x $i (fun xi => xi / $xi))

macro x:ident noWs "[" ids:term,* "]" " •= " xi:term : doElem => do
  let i ← mkTuple ids.getElems
  `(doElem| $x:ident := ArrayType.modify $x $i (fun xi => $xi • xi))


@[app_unexpander ArrayType.get] def unexpandArrayTypeGet : Lean.PrettyPrinter.Unexpander
  | `($(_) $x ($i, $is,*)) => `($x[$i:term,$[$is:term],*])
  | `($(_) $x $i) => `($x[$i:term])
  | _ => throw ()


----------------------------------------------------------------------------------------------------


-- Notation: ⊞ i => f i --
--------------------------

open Lean.TSyntax.Compat in
-- macro "⊞ " x:term " => " b:term:51 : term => `(introElemNotation fun $x => $b)
-- macro "⊞ " x:term " : " X:term " => " b:term:51 : term => `(introElemNotation fun ($x : $X) => $b)

-- The `by exact` is a hack to make certain case work
--    see: https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/uncurry.20fails.20with.20.60Icc.60
open Term Function Lean Elab Term Meta in
elab "⊞ " xs:funBinder* " => " b:term:51 : term  => do
  let fn ← elabTermAndSynthesize (← `(fun $xs* => $b)) none
  let arity := (← inferType fn).getNumHeadForalls
  try
    -- uncurry if necessary
    let fn ←
      if arity = 1 then
        pure fn
      else
        mkAppM ``HasUncurry.uncurry #[fn]

    let .some (Idx, Elem) := (← inferType fn).arrow?
      | throwError "⊞ _ => _: expectes function type {← ppExpr (← inferType fn)}"

    let Cont ← mkAppOptM `SciLean.DataArrayN #[Elem, none, Idx, none]

    mkAppOptM ``ArrayType.ofFn #[Cont, Idx, Elem, none, fn]
  catch e =>
    if arity = 1 then
      elabTerm (← `(ArrayType.ofFn fun $xs* => $b)) none
    else if arity = 2 then
      elabTerm (← `(ArrayType.ofFn (Function.uncurry fun $xs* => $b))) none
    else
      throwError "notation `⊞ _ => _` is not supported for high rank arrays when types are unknown\
                  \nplease specify the types!\n{e.toMessageData}"



-- Notation: ⊞[1,2,3] --
------------------------

/-- A notation for creating a `DataArray` from a list of elements. -/
syntax (name := dataArrayNotation) (priority:=high)
  "⊞[" ppRealGroup(sepBy1(ppGroup(term,+,?), ";", "; ", allowTrailingSep)) "]" : term


open Lean Qq Elab Term in
/-- Elaborate a `⊞[...]` notation into a `ArrayType.ofFn` term. -/
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

    if rows.size = 1 then
      let dataArray := mkIdent `SciLean.DataArrayN
      let fn ←
        elabTerm (←`(@ArrayType.ofFn ($dataArray _ _) _ _ _
                      fun (i : Fin $n) => [$elems,*].get! i.1)) none

      return fn
    else
      let dataArray := mkIdent `SciLean.DataArrayN
      let fn ←
        elabTerm (←`(@ArrayType.ofFn ($dataArray _ _) _ _ _
                      fun ((i,j) : Fin $m × Fin $n) => [$elems,*].get! (IndexType.toFin (i,j)).1)) none
      return fn



@[app_unexpander ArrayType.ofFn]
def unexpandArrayTypeOfFnNotation : Lean.PrettyPrinter.Unexpander
  | `($(_) $f) =>
    match f with
    | `(fun $_ => [$xs,*].get! ↑$_) =>
      `(⊞[$xs,*])
    | `(fun $x => $b) =>
      `(⊞ $x:term => $b)
    | `(HasUncurry.uncurry (fun $xs* => $b)) =>
      `(⊞ $xs* => $b)
    | `(↿fun $xs* => $b) =>
      `(⊞ $xs* => $b)
    | _ => throw ()
  | _  => throw ()


-- Notation: Float ^ Idx n --
-----------------------------

namespace ArrayType.PowerNotation

-- Notation: Float^[10,20] --
-----------------------------

declare_syntax_cat dimSpec
syntax term : dimSpec
syntax (priority:=high) "[" dimSpec,+ "]" : dimSpec
syntax "[" term ":" term "]": dimSpec

/-- `x^[y]` is either array type or iterated function depending on the type of `x`.

**iterated function** `f^[n]` call `f` n-times e.g. `f^[3] = f∘f∘f`

**type product** `Float^[n]` array of n elemts with values in `Float`

The array notation is quite flexible and allows you to create arrays arrayType with various types.
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

  let I ← expand' ns.getElems.toList
  -- let C ← mkFreshTypeMVar
  -- let inst ← synthInstance <| mkAppN (← mkConstWithFreshMVarLevels ``ArrayTypeNotation) #[C,Y,X]
  -- let C ← whnfR (← instantiateMVars C)
  -- let result ← instantiateMVars <| ← mkAppOptM ``arrayTypeCont #[Y,X,C,inst]
  return ← mkAppOptM `SciLean.DataArrayN #[X,none,I,none] --result.getRevArg! 1

end ArrayType.PowerNotation
