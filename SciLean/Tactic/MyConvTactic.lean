import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Conv.Basic

namespace Lean.Elab.Tactic.Conv 
open Meta



syntax (name := print_lhs) "print_lhs" : conv
syntax (name := print_rhs) "print_rhs" : conv
syntax (name := add_id) "add_id" : conv
syntax (name := add_foo) "add_foo" : conv


@[tactic print_lhs] def printLhs : Tactic := fun stx => do
  match stx with
  | `(conv| print_lhs) => do
    let lhs ← getLhs
    IO.println lhs
    -- dbg_trace lhs
  | _ => throwUnsupportedSyntax

@[tactic print_rhs] def printRhs : Tactic := fun stx => do
  match stx with
  | `(conv| print_rhs) => do
    let rhs ← getRhs
    IO.println rhs
    -- dbg_trace rhs
  | _ => throwUnsupportedSyntax

theorem id_eq {α} (a : α) : a = id a := by rfl

@[tactic add_id] def addId : Tactic := fun stx => do
  match stx with
  | `(conv| add_id) => do
    let lhs ← getLhs
    let lhs' ← mkAppM `id #[lhs]
    let eq ← mkAppM `Lean.Elab.Tactic.Conv.id_eq #[lhs]
    updateLhs lhs' eq
    -- dbg_trace rhs
  | _ => throwUnsupportedSyntax

-- @[irreducible]
def foo {α} (a : α) := a

@[tactic add_foo] def addFoo : Tactic := fun stx => do
  match stx with
  | `(conv| add_foo) => do
    let lhs ← getLhs
    let lhs' ← mkAppM `Lean.Elab.Tactic.Conv.foo #[lhs]
    let eqGoal ← mkFreshExprSyntheticOpaqueMVar (← mkEq lhs' lhs)

    updateLhs lhs' eqGoal

    replaceMainGoal [eqGoal.mvarId!, (← getMainGoal)]
  | _ => throwUnsupportedSyntax


example (x y z : Nat) : (x + y) + z = (x + (foo y + z)) := 
by
  conv =>
    enter [1,1,2]
    add_foo; (tactic => unfold foo; rfl)
    
  .
  apply Nat.add_assoc
  done
