/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import SciLean.Tactic.FunTrans.Elab
import SciLean.Tactic.LSimp

namespace SciLean.Tactic
open Lean Meta Elab Tactic Mathlib.Meta.FunTrans Lean.Parser.Tactic


syntax (name := lfunTransTacStx) "lfun_trans" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)? : tactic

syntax (name := lfunTransConvStx) "lfun_trans" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*) "]")? : conv


@[tactic lfunTransTacStx]
def lfunTransTac : Tactic := fun stx => do
  match stx with
  | `(tactic| lfun_trans $cfg $[$disch]? $[only]? $[[$a,*]]? $[$loc]?) => do

    -- set fun_trans config
    funTransContext.modify
      fun c => { c with funPropContext := { c.funPropContext with disch := stxToDischarge disch}}

    let a := a.getD (Syntax.TSepArray.mk #[])
    if stx[3].isNone then
      evalTactic (← `(tactic| lsimp $cfg $[$disch]? [↓fun_trans_simproc,$a,*]))
    else
      evalTactic (← `(tactic| lsimp $cfg $[$disch]? only [↓fun_trans_simproc,$a,*]))

    -- reset fun_trans config
    funTransContext.modify fun _ => {}

  | _ => throwUnsupportedSyntax


@[tactic lfunTransConvStx]
def lfunTransConv : Tactic := fun stx => do
  match stx with
  | `(conv| lfun_trans $cfg $[$disch]? $[only]? $[[$a,*]]?) => do

    -- set fun_trans config
    funTransContext.modify
      fun c => { c with funPropContext := { c.funPropContext with disch := stxToDischarge disch}}

    let a := a.getD (Syntax.TSepArray.mk #[])
    if stx[3].isNone then
      evalTactic (← `(conv| lsimp $cfg $[$disch]? [↓fun_trans_simproc,$a,*]))
    else
      evalTactic (← `(conv| lsimp $cfg $[$disch]? only [↓fun_trans_simproc,$a,*]))

    -- reset fun_trans config
    funTransContext.modify fun _ => {}

  | _ => throwUnsupportedSyntax


-- @[tactic lfunTransTacticStx]
-- def lfunTransTactic : Tactic := fun stx => do
--   match stx with
--   | `(tactic| lfun_trans $[$cfg]? $[$disch]? $[only]? $[[$a,*]]?) => do

--     -- set fun_trans config
--     funTransContext.modify
--       fun c => { c with funPropContext := { c.funPropContext with disch := stxToDischarge disch}}

--     let a := a.getD (Syntax.TSepArray.mk #[])
--     if stx[3].isNone then
--       evalTactic (← `(tactic| lsimp $[$cfg]? $[$disch]? [↓fun_trans_simproc,$a,*]))
--     else
--       evalTactic (← `(tactic| lsimp $[$cfg]? $[$disch]? only [↓fun_trans_simproc,$a,*]))

--     -- reset fun_trans config
--     funTransContext.modify fun _ => {}

--   | _ => throwUnsupportedSyntax
