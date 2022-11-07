import SciLean.Tactic.CustomSimp.DebugSimp
import SciLean.Core

import Lean.Meta
import Lean.Parser
import Lean.Elab

-- namespace Lean.Elab.Tactic
open Lean Meta Simp

open SciLean

open Lean.Parser.Tactic in
syntax (name := custom_simp) "custom_simp " (config)? (discharger)? (&"only ")? ("[" (simpStar <|> simpErase <|> simpLemma),* "]")? (location)? : tactic

open Lean.Elab.Tactic in
@[tactic custom_simp] def evalCustomSimp : Tactic := fun stx => do
  let { ctx, dischargeWrapper } ← withMainContext <| mkSimpContext stx (eraseLocal := false)
  let usedSimps ← dischargeWrapper.with fun discharge? =>
    SciLean.Meta.CustomSimp.simpLocation ctx discharge? (expandOptLocation stx[5]) #[] #[]
  if tactic.simp.trace.get (← getOptions) then
    dbg_trace "warning: Runnig custom simp with tracing, not sure if it is working properly!"
    traceSimpCall stx usedSimps


variable {α β γ δ : Type}

def D {α β : Type} (f : α → β) : α → α → β := sorry

theorem D_comp  -- {α β γ : Type}
  (f : β → γ) (g : α → β)
  : D (λ x => f (g x)) = λ x dx => D f (g x) (D g x dx) := sorry


@[simp_guard g (λ (x : α) => x)]
theorem D_comp_parm
  (f : β → δ → γ) (g : α → β) (d : δ)
  : D (λ x => f (g x) d) = λ x dx => D (λ y => f y d) (g x) (D g x dx) :=
by
  apply D_comp (λ y => f y d) g -- we have to specify `f` explicitly


example
  (f : β → δ → γ) (g : α → β) (d : δ)
  : D (λ x => f (g x) d) = λ x dx => D (λ y => f y d) (g x) (D g x dx) :=
by
  -- simp [D_comp_parm] -- normal `simp` fails with timeout
  custom_simp [D_comp_parm] -- our `custom_simp` with a simp guard solves this goal
  done
