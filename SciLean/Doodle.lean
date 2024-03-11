import SciLean

open SciLean

variable
  {R : Type} [RealScalar R]

set_default_scalar R

-- fprop example
example : CDifferentiable R fun x : R => x^2 := by simp (config:={zeta:=true})
-- ftrans example
example : ∂ x : R, x^2 = fun x => 2 * x := by conv => lhs; ftrans

-- derivative
-- ∂ : (R→X) → (R→X)
#check ∂ x : R, (x^2)
#check ∂! x : R, (x^2)


-- gradient
-- ∇ : (X→R) → (X→X)
#check ∇ x : R×R, x.1
#check ∇! x : R×R, x.1
#check ∇! x : R×R, ‖x‖₂²



-- forward AD
-- ∂> : (X→Y) → (X→X→Y×Y)
#check ∂> x : R, x^2
#check ∂>! x : R, x^2


-- reverse AD
-- <∂ : (X→Y) → (X→Y×(Y→X))
#check <∂! x : R×R, x.1


------------------------------------------------

def foo (x y : R) : R := x + y^2

#generate_fwdCDeriv foo x y
  prop_by unfold foo; fprop
  trans_by unfold foo; ftrans

#print foo.arg_xy.CDifferentiable_rule
#print foo.arg_xy.fwdCDeriv
#check foo.arg_xy.fwdCDeriv_rule

#check ∂>! x : R, foo x x




variable (n m : Nat) (x : Float^[n]) (y : Float^[m])

#check ⊞ i (j : Fin m) => (x[i] : Float)^j.1


#check ⊞ i j => x[i] * y[j]


#check introElemNotation (Function.HasUncurry.uncurry (fun ((i,j) : Fin n × Fin m) => (x[i] : Float)^j.1))

#check ↿(fun ((i,j) : Fin n × Fin m) => (x[i] : Float)^j.1)


#check ↿(fun i => (x[i] : Float))


#check LeanColls.Indexed.ofFn (C:=DataArrayN Float _) (Function.HasUncurry.uncurry fun i (j : Fin m) => (x[i] : Float)^j.1)

#check LeanColls.Indexed.ofFn (C:=DataArrayN Float _) (↿fun i (j : Fin m) => (x[i] : Float)^j.1)

open Lean Elab Term Meta

/-- Assuming `e = X₁ × ... Xₘ` this function returns `#[X₁, ..., Xₘ]`.

You can provide the expected number `n?` of elemnts then this function returns
`#[X₁, ..., (Xₙ × ... Xₘ)].

Returns none if `n? = 0` or `n? > m` i.e. `e` does not have enough terms.
-/
private partial def splitProdType (e : Expr) (n? : Option Nat := none)  : Option (Array Expr) :=
  if n? = .some 0 then
    none
  else
    go e #[]
  where
    go (e : Expr) (xs : Array Expr) : Option (Array Expr) :=
      if .some (xs.size + 1) = n? then
        xs.push e
      else
        if e.isAppOfArity ``Prod 2 then
          go (e.getArg! 1) (xs.push (e.getArg! 0))
        else
          if n?.isNone then
            xs.push e
          else
            .none

private def mkProdElem (xs : Array Expr) : MetaM Expr :=
  match xs.size with
  | 0 => return default
  | 1 => return xs[0]!
  | _ =>
    let n := xs.size
    xs[0:n-1].foldrM (init:=xs[n-1]!) fun x p => mkAppM ``Prod.mk #[x,p]


/-- Turn an array of terms in into a tuple. -/
private def mkTuple (xs : Array (TSyntax `term)) : MacroM (TSyntax `term) :=
  `(term| ($(xs[0]!), $(xs[1:]),*))


open Lean Elab LeanColls Indexed Notation Term Meta

syntax:max (name:=indexedGet) (priority:=high+1) term noWs "[" elemIndex,* "]" : term

@[term_elab indexedGet]
def elabFoo : Term.TermElab := fun stx expectedType? => do
  match stx with
| `($x[$ids:elemIndex,*]) => do

  IO.println "asdfads"

  let ids := ids.getElems

  let getElemFallback : TermElabM (Option Expr) := do
    if ids.size ≠ 1 then
      return none
    match ids[0]! with
    | `(elemIndex| $i:term) => elabTerm (← `(getElem $x $i (by get_elem_tactic))) none
    | `(elemIndex| $i : $j) => elabTerm (← `(let a := $x; Array.toSubarray a $i $j)) none
    | `(elemIndex| $i :) => elabTerm (← `(let a := $x; Array.toSubarray a $i a.size)) none
    | `(elemIndex| : $j) => elabTerm (← `(let a := $x; Array.toSubarray a 0 $j)) none
    | _ => return none


  let x ← elabTerm x none
  let X ← inferType x
  let I ← mkFreshTypeMVar
  let E ← mkFreshTypeMVar
  let indexed := (mkAppN (← mkConstWithFreshMVarLevels ``Indexed) #[X, I, E])
  let .some inst ← synthInstance? indexed
    | if let .some xi ← getElemFallback then
         return xi
      else
        throwError s!"`{← ppExpr x} : {← ppExpr X}` is not indexed type.
Please provide instance `Indexed {← ppExpr X} ?I ?E`."


| _ => throwError "asdf"


#check ↿fun i j => x[i] * y[j]

open Lean Elab Term in
elab (priority:=high+1) x:term noWs "[" i:term "]" : term => do
  elabTerm (← `(GetElem.getElem $x $i True.intro)) none
