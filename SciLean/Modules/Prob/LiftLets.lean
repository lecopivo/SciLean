import Mathlib.Tactic.LiftLets

-- TODO: move this to mathlib
open Lean in
syntax (name := lift_lets) "lift_lets" (Parser.Tactic.config)? : conv

open Lean Meta Elab Tactic Mathlib.Tactic Lean.Elab.Tactic.Conv in
elab_rules : tactic
  | `(conv| lift_lets) => do -- $[$cfg:config]? $[$loc:location]?
    let lhs ← getLhs
    let lhs' ← lhs.liftLets mkLetFVars {}
    changeLhs lhs'
