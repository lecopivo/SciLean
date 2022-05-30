import SciLean.Tactic.CustomSimp.Main
import SciLean.Core

import Lean.Meta
import Lean.Parser
import Lean.Elab

-- namespace Lean.Elab.Tactic
open Lean Meta Simp

namespace SciLean.DebugSimp

def pre (e : Expr) : SimpM Step := do
  trace[Meta.Tactic.simp] "Running pre on {← ppExpr e}"
  pure (Step.visit (Result.mk e none))

def post (e : Expr) : SimpM Step := do
  trace[Meta.Tactic.simp] "Running post on {← ppExpr e}"
  pure (Step.visit (Result.mk e none))


open Lean.Parser.Tactic in
syntax (name := debug_simp) "debug_simp " (config)? (discharger)? (&"only ")? ("[" (simpStar <|> simpErase <|> simpLemma),* "]")? (location)? : tactic

open Lean.Elab.Tactic in
@[tactic debug_simp] def evalDebugSimp : Tactic := fun stx => do
  let r ← withMainContext <| mkSimpContext stx (eraseLocal := false)
  r.dischargeWrapper.with fun discharge? =>
    SciLean.Tactic.CustomSimp.simpLocation r.ctx discharge? r.fvarIdToLemmaId (expandOptLocation stx[5]) #[pre] #[post]

-- constant foo : Nat → Nat
-- class Foo (n : Nat)

-- theorem foo_zero (n) [Foo n] : foo n = 0 := sorry

-- set_option trace.Meta.Tactic.simp true in
-- set_option trace.Meta.Tactic.simp.unify true in
-- set_option trace.Meta.Tactic.simp.discharge true in
-- example (op : Nat → Nat → Nat) (a b c : Nat) :
--   op (foo a) (foo $ op (foo (foo a)) (foo $ op b c)) = 0 :=
-- by
--   debug_simp [↓foo_zero]
--   admit


-- def bar (f : Nat → Nat) := λ a b : Nat => f b

-- theorem bar_simp (f : Nat → Nat) (a b : Nat) : bar f a b = f b := by simp[bar]

-- -- -- works
-- -- example (f : Nat → Nat) : bar f a (bar f b c) = f (f c) := by debug_simp (config := {singlePass := true}) only [↓bar_simp]

-- -- does not work
-- set_option trace.Meta.Tactic.simp true in
-- example : bar (λ x => x) a (bar (λ x => x) b c) = c := by debug_simp (config := {singlePass := true}) only [↓bar_simp]
