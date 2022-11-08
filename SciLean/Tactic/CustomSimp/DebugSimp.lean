import SciLean.Tactic.CustomSimp.Main

import Lean.Meta
import Lean.Parser
import Lean.Elab

-- namespace Lean.Elab.Tactic
open Lean Meta Simp

namespace SciLean.Meta.DebugSimp

def pre (e : Expr) : SimpM Step := do
  trace[Meta.Tactic.simp] "Running pre on {← ppExpr e}"
  pure (Step.visit (Result.mk e none 0))

def post (e : Expr) : SimpM Step := do
  trace[Meta.Tactic.simp] "Running post on {← ppExpr e}"
  pure (Step.visit (Result.mk e none 0))


open Lean.Parser.Tactic in
syntax (name := debug_simp) "debug_simp " (config)? (discharger)? (&"only ")? ("[" (simpStar <|> simpErase <|> simpLemma),* "]")? (location)? : tactic


open Lean.Elab.Tactic in
@[tactic debug_simp] def evalDebugSimp : Tactic := fun stx => do
  let { ctx, dischargeWrapper } ← withMainContext <| mkSimpContext stx (eraseLocal := false)
  let usedSimps ← dischargeWrapper.with fun discharge? =>
    SciLean.Meta.CustomSimp.simpLocation ctx discharge? (expandOptLocation stx[5]) #[pre] #[post]
  if tactic.simp.trace.get (← getOptions) then
    dbg_trace "warning: Runnig custom simp with tracing, not sure if it is working properly!"
    traceSimpCall stx usedSimps

opaque foo : Nat → Nat
class Foo (n : Nat)

-- @[simp_guard n 0]
-- theorem foo_zero (n) [Foo n] : foo n = 0 := sorry

@[simp_guard f foo]
theorem foo_fun_zero {α : Type} [Foo n] (f : α → Nat) (a : α) : foo (f a) = 0 := sorry

set_option trace.Meta.Tactic.simp true in
set_option trace.Meta.Tactic.simp.unify true in
set_option trace.Meta.Tactic.simp.discharge true in
example (op : Nat → Nat → Nat) (a b c : Nat) :
  op (foo (foo a)) (foo $ op (foo (foo 0)) (foo $ op b c)) = 0 := 
by
  -- debug_simp [↓foo_zero]
  debug_simp [↓foo_fun_zero]
  admit


-- def bar (f : Nat → Nat) := λ a b : Nat => f b

-- theorem bar_simp (f : Nat → Nat) (a b : Nat) : bar f a b = f b := by simp[bar]

-- -- -- works
-- -- example (f : Nat → Nat) : bar f a (bar f b c) = f (f c) := by debug_simp (config := {singlePass := true}) only [↓bar_simp]

-- -- does not work
-- set_option trace.Meta.Tactic.simp true in
-- example : bar (λ x => x) a (bar (λ x => x) b c) = c := by debug_simp (config := {singlePass := true}) only [↓bar_simp]
