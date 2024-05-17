import Lean.Elab.Tactic.Conv

import SciLean.Tactic.GTrans.Core
import SciLean.Util.RewriteBy

namespace SciLean

namespace Tactic.GTrans

open Lean Meta Elab Tactic

syntax (name:=gtrans_tac) "gtrans" : tactic

/-- `gtrans` as conv tactic will fill in meta variables in generalized transformation -/
syntax (name:=gtrans_conv) "gtrans" : conv


@[tactic gtrans_tac] unsafe def gtransTac : Tactic := fun _ => do
  let goal ← getMainGoal

  let e ← goal.getType

  let .some prf ← gtrans 100 e
    | throwError "gtrans: faild to prove {← ppExpr e}"

  goal.assignIfDefeq prf


@[tactic gtrans_conv] unsafe def gtransConv : Tactic := fun _ => do
  let e ← Conv.getLhs

  let .some _ ← gtrans 100 e
    | throwError "gtrans: faild to prove {← ppExpr e}"

  -- goal.assignIfDefeq prf


open Lean Elab Term Meta Qq in
/-- `gtrans_output t by gtrans` returns tuple of all output parameters infered by `gtrans` in the term `t` -/
elab "gtrans_output" t:term "by" c:Parser.Tactic.Conv.convSeq : term => do

  let e ← elabTerm (← `($t rewrite_by $c)) none

  forallTelescope e fun xs b => do

    let fn := b.getAppFn
    forallTelescope (← inferType fn) fun ys _ => do

    let mut output : Array Expr := #[]

    for y in ys, arg in b.getAppArgs do
      if (← inferType y).isAppOf ``outParam then
        output := output.push arg

    mkLambdaFVars xs (← mkProdElem output)

/-- `gtrans_output t` returns tuple of all output parameters infered by `gtrans` in the term `t`.

This is a shorthand for `gtrans_output t by gtrans`. -/
macro "gtrans_output" t:term : term => `(gtrans_output $t by gtrans)
