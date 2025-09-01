import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Conv.Basic

import SciLean.Lean.Expr


namespace SciLean.Meta

open Lean Meta Elab Tactic Conv


syntax (name := let_move_up) " let_move_up " ident (num)? : conv
syntax (name := let_move_down) " let_move_down " ident (num)? : conv


syntax (name := let_add) " let_add " ident term : conv

@[tactic let_add]
def convLetAdd : Tactic
| `(conv| let_add $id:ident $val:term) => do
  (← getMainGoal).withContext do
    let lhs ← getLhs
    let xName := id.getId
    let xValue ← elabTerm val none
    let xType ← inferType xValue

    changeLhs (.letE xName xType xValue lhs false)
| _ => Lean.Elab.throwUnsupportedSyntax


syntax (name := let_unfold) " let_unfold " ident : conv

def letUnfold (e : Expr) (id : Name) : Expr :=
  e.replace λ e =>
    if e.isLet && e.letName! = id then
      some (e.letBody!.instantiate1 e.letValue!)
    else
      none

@[tactic let_unfold]
def convLetUnfold : Tactic
| `(conv| let_unfold $id:ident) => do
  (← getMainGoal).withContext do
    let lhs ← getLhs

    changeLhs (letUnfold lhs id.getId)
| _ => Lean.Elab.throwUnsupportedSyntax

macro " let_unfold " id:ident : tactic => `(tactic| conv => let_unfold $id)

syntax (name := let_unfold1) " let_unfold1 " ident (num)? : conv

def letUnfold1 (e : Expr) (id : Name) (nth := 0) : Expr := Id.run do
  e.replaceM λ e =>
    if e.isLet && e.letName! = id then
      let b' := e.letBody!.instantiateOnce e.letValue! 0 nth
      return .done (.letE e.letName! e.letType! e.letValue! b' false)
    else
      return .noMatch

@[tactic let_unfold1]
def convLetUnfold1 : Tactic
| `(conv| let_unfold1 $id:ident $[$n:num]?) => do
  (← getMainGoal).withContext do
    let lhs ← getLhs

    let n := n.map (λ n => n.getNat) |>.getD 0
    changeLhs (letUnfold1 lhs id.getId n)
| _ => Lean.Elab.throwUnsupportedSyntax

macro " let_unfold1 " id:ident n:(num)? : tactic => `(tactic| conv => let_unfold1 $id $[$n]?)


/-- Moves let binding upwards, maximum by `n?` positions. Returns none if there is no such let binding.

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
  run e |>.map λ (e, _) => e
where
  run (e : Expr) : Option (Expr×Nat) :=
    match e with
    | .app f x =>

      if let .some (x', n') := run x then
        if (n?.isNone || (n' < n?.get!)) &&
          x'.isLet && p x'.letName! then
          some (.letE x'.letName! x'.letType! x'.letValue! (.app (f.liftLooseBVars 0 1) x'.letBody!) false,
                n'+1)
        else
          some (.app f x', n')

      else if let .some (f', n') := run f then
        if (n?.isNone || (n' < n?.get!)) &&
           f'.isLet && p f'.letName! then
          some (.letE f'.letName! f'.letType! f'.letValue! (.app f'.letBody! (x.liftLooseBVars 0 1)) false,
                n'+1)
        else
          some (.app f' x, n')

      else
        none

    | .letE xName xType xValue b _ =>

      if let .some (b', n') := run b then

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
      if let .some (b', n') := run b then

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



-- /-- Moves let binding down, maximum by `n?` positions. Returns none if there is no such let binding.

-- For example for the following expresion
-- ```
--   let x := ..
--   let y := ..
--   let z := ..
--   f x y z
-- ```
-- calling `letMoveUp e (λ n => n == `x) (some 2)` will produce
-- ```
--   let y := ..
--   let z := ..
--   let x := ..
--   f x y z
-- ```
-- but only if the value of `y` does not depend on `z`.


-- Let binding is specified by a running `p` on let binding name.
-- -/
-- def letMoveDown (e : Expr) (p : Name → Bool) (n? : Option Nat) : Option Expr := do
--   if n?.isSome && n?.get! = 0 then
--     some e
--   else
--   match e with
--   | .app f x =>
--     if let .some x' := letMoveDown x p n? then
--       some (.app f x')
--     else if let .some f' := letMoveDown f p n? then
--       some (.app f' x)
--     else
--       none

--   | .letE xName xType xValue b _ =>

--     if p xName then
--       match b with
--       | .letE yName yType yValue b' _ => sorry

--       | .lam yName yType b' bi => sorry
--       | _ => some e
--     else

--       if let .some b' := letMoveDown b p n? then
--         some (.letE xName xType xValue b' false)
--       else
--         none


--   | _ => none



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
    let_add hihi 10
    let_unfold1 a
    let_unfold1 a
    let_unfold1 a
    let_unfold1 a
    let_unfold1 a
