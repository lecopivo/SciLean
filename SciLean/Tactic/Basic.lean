import Lean

import SciLean.Lean.Expr
import SciLean.Lean.Meta.Basic

open Lean

namespace Lean.Parser.Tactic.Conv

  macro "no_op" : conv => `(conv| tactic' => skip)

  syntax "repeat' " convSeq : conv
  macro_rules
    | `(conv| repeat' $seq) => `(conv| first | ($seq); repeat' $seq | no_op)


end Lean.Parser.Tactic.Conv


syntax (name := flatten_let_conv) " flatten_let ": conv
syntax (name := flatten_let_tactic) " flatten_let ": tactic

open Lean Meta Elab Tactic Conv
open Lean.Parser.Tactic


@[tactic flatten_let_conv] def convFlattenLet : Tactic
| `(conv| flatten_let) => do
  (← getMainGoal).withContext do
    let lhs ← getLhs
    let lhs' ← flattenLet 20 (← instantiateMVars lhs)

    changeLhs lhs'
| _ => Lean.Elab.throwUnsupportedSyntax

@[tactic flatten_let_tactic] def tacticFlattenLet : Tactic
| `(tactic| flatten_let) => do
  let goal ← getMainGoal
  goal.withContext do
    let t ← goal.getType
    let t' ← flattenLet 20 t

    let newGoal ← mkFreshExprMVar t'
    let eqGoal ← mkFreshExprMVar (← mkEq t t')
    eqGoal.mvarId!.refl

    goal.assign (← mkAppM ``Eq.mpr #[eqGoal, newGoal])
    replaceMainGoal [newGoal.mvarId!]

| _ => Lean.Elab.throwUnsupportedSyntax


macro "rw'" " [" s:simpLemma,* "]" : conv =>
  let s' : Syntax.TSepArray `Lean.Parser.Tactic.simpStar "," := ⟨s.1⟩ -- hack
  `(conv| simp (config := {zeta := false, proj := false, beta := false, iota := false, eta := false, singlePass := true, decide := false}) only [$s',*])

macro "rw'" " [" s:simpLemma,* "]" : tactic =>
  let s' : Syntax.TSepArray `Lean.Parser.Tactic.simpStar "," := ⟨s.1⟩ -- hack
  `(tactic| simp (config := {zeta := false, proj := false, beta := false, iota := false, eta := false, singlePass := true, decide := false}) only [$s',*])


macro "clean_up" : tactic => `(tactic| conv => enter[1]; dsimp (config := {zeta := false, proj:=false}); flatten_let)
macro "clean_up_simp" : tactic => `(tactic| conv => enter[1]; simp (config := {zeta := false, proj:=false}); flatten_let)

macro "clean_up" : conv => `(conv| (dsimp (config := {zeta := false, proj:=false}); flatten_let))
macro "clean_up_simp" : conv => `(conv| (simp (config := {zeta := false, proj:=false}); flatten_let))
