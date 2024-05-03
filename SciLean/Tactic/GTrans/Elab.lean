import Lean.Elab.Tactic.Conv

import SciLean.Tactic.GTrans.Core

namespace SciLean

namespace Tactic.GTrans

open Lean Meta Elab Tactic

syntax (name:=gtrans_tac) "gtrans" : tactic

/-- `gtrans` as conv tactic will fill in meta variables in generalized transformation -/
syntax (name:=gtrans_conv) "gtrans" : conv


@[tactic gtrans_tac] def gtransTac : Tactic := fun _ => do
  let goal ← getMainGoal

  let e ← goal.getType

  let .some prf ← gtrans 100 e
    | throwError "gtrans: faild to prove {← ppExpr e}"

  goal.assignIfDefeq prf


@[tactic gtrans_conv] def gtransConv : Tactic := fun _ => do
  let e ← Conv.getLhs

  let .some _ ← gtrans 100 e
    | throwError "gtrans: faild to prove {← ppExpr e}"

  -- goal.assignIfDefeq prf
