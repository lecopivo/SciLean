import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Conv.Basic

namespace Lean.Elab.Tactic.Conv 
open Meta



syntax (name := print_lhs) "print_lhs" : conv
syntax (name := print_rhs) "print_rhs" : conv
syntax (name := add_id) "add_id" : conv
syntax (name := add_foo) "add_foo" : conv



open Lean Meta Elab Tactic Conv

syntax (name := let_move_up) " let_move_up " ident (num)? : conv 
syntax (name := let_move_down) " let_move_down " ident (num)? : conv 
syntax (name := let_unfold) " let_unfold " ident : conv 


def _root_.Lean.Expr.myPrint : Expr → String 
| .const n _ => n.toString
| .bvar n => s!"[{n}]"
| .app f x => f.myPrint ++ " " ++ x.myPrint
| .lam n t x bi => s!"fun {n} => {x.myPrint}"
| .letE n t v x _ => s!"let {n} := {v.myPrint}; {x.myPrint}"
| _ => "??"

/--
  Swaps bvars indices `i` and `j`

  NOTE: the indices `i` and `j` do not correspond to the `n` in `bvar n`. Rather
  they behave like indices in `Expr.lowerLooseBVars`, `Expr.liftLooseBVars`, etc.

  TODO: This has to have a better implementation, but I'm still beyond confused with how bvar indices work
-/
def _root_.Lean.Expr.swapBVars (e : Expr) (i j : Nat) : Expr := 

  let swapBVarArray : Array Expr := Id.run do
    let mut a : Array Expr := .mkEmpty e.looseBVarRange
    for k in [0:e.looseBVarRange] do
      a := a.push (.bvar (if k = i then j else if k = j then i else k))
    a

  e.instantiate swapBVarArray

/-- Moves let binding upwards, maximum by `n?` positions.
  
For example for the following expresion 
```  
  let x := ..
  let y := ..
  let z := ..
  f x y z
```
calling `letMoveUp e (λ n => n == `z) (some 1)` will produce
```
  let x := ..
  let z := ..
  let y := ..
  f x y z
```
but only if the value of `y` does not depend on `z`.

Changing `(some 1)` to `(some 2)` or `none`, `let z := ...` will be move to the top.
-/
def letMoveUp (e : Expr) (p : Name → Bool) (n? : Option Nat) : Option Expr := do
  run e 0 |>.map λ (e, _) => e
where
  run (e : Expr) (bLvl : Nat) : Option (Expr×Nat) :=
    match e with
    | .app f x => 

      if let .some (x', n') := run x bLvl then
        if (n?.isNone || (n' < n?.get!)) &&
          x'.isLet && p x'.letName! then 
          some (.letE x'.letName! x'.letType! x'.letValue! (.app (f.liftLooseBVars 0 1) x'.letBody!) false,
                n'+1)
        else
          some (.app f x', n')

      else if let .some (f', n') := run f bLvl then
        if (n?.isNone || (n' < n?.get!)) &&
           f'.isLet && p f'.letName! then 
          some (.letE f'.letName! f'.letType! f'.letValue! (.app f'.letBody! (x.liftLooseBVars 0 1)) false,
                n'+1)
        else
          some (.app f' x, n')

      else
        none

    | .letE xName xType xValue b _ => 

      if let .some (b', n') := run b (bLvl+1) then

        if (n?.isNone || (n' < n?.get!)) &&
           b'.isLet && p b'.letName! &&
           ¬(b'.letType!.hasLooseBVar 0) && ¬(b'.letValue!.hasLooseBVar 0)then 
          let yName := b'.letName!
          let yType := b'.letType!
          let yValue := b'.letValue!

          let b'' := b'.letBody!.swapBVars 0 1
          some (.letE yName (yType.lowerLooseBVars 1 1) (yValue.lowerLooseBVars 1 1)
                  (.letE xName (xType.liftLooseBVars 0 1) (xValue.liftLooseBVars 0 1) b'' false) false,
                n'+1)
        else
          some (.letE xName xType xValue b' false, n')
      else if p xName then
        some (e, 0)
      else
        none

    | .lam xName xType b bi => 
      if let .some (b', n') := run b (bLvl+1) then

        if (n?.isNone || (n' < n?.get!)) &&
           b'.isLet && p b'.letName! &&
           ¬(b'.letType!.hasLooseBVar 0) && ¬(b'.letValue!.hasLooseBVar 0)then 
          let yName := b'.letName!
          let yType := b'.letType!
          let yValue := b'.letValue!
          let b'' := b'.letBody!.swapBVars 0 1
          some (.letE yName (yType.lowerLooseBVars 1 1) (yValue.lowerLooseBVars 1 1)
                  (.lam xName (xType.liftLooseBVars 0 1) b'' bi) false,
                n'+1)
        else
          some (.lam xName xType b' bi, n')
      else
        none

    | _ => none

@[tactic let_move_up] 
def convLetMoveUp : Tactic
| `(conv| let_move_up $id:ident $[$n:num]?) => do  
  (← getMainGoal).withContext do
    let lhs ← getLhs
    if let .some lhs':= letMoveUp lhs (λ n => n.eraseMacroScopes == id.getId) (n.map λ n => n.getNat) then
      changeLhs lhs'
| _ => Lean.Elab.throwUnsupportedSyntax

macro " let_move_up " id:ident n:(num)? : tactic => `(tactic| conv => let_move_up $id $[$n]?)

example 
  : (λ x : Nat => 
      let a := x
      let b := x + a
      λ y => 
      let c := x + a + b + y
      let d := x + a + b
      a + b + (let z := 10; c + z) + d + y)
    = 
    (λ x : Nat => 
      let a := x
      let b := x + a
      λ y => 
      let c := x + a + b + y
      let d := x + a + b
      a + b + (let z := 10; c + z) + d + y)
  := 
by
  conv => 
    lhs
    let_move_up z
    let_move_up d
  

#exit
