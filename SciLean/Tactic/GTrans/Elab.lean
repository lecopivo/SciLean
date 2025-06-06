import Lean.Elab.Tactic.Conv

import SciLean.Tactic.GTrans.Core
import SciLean.Util.RewriteBy
import SciLean.Tactic.InferVar

import Mathlib.Tactic.FunProp.Elab

namespace SciLean

namespace Tactic.GTrans

open Lean Meta Elab Tactic

syntax (name:=gtrans_tac) "gtrans" : tactic

/-- `gtrans` as conv tactic will fill in meta variables in generalized transformation -/
syntax (name:=gtrans_conv) "gtrans" : conv

open Lean.Parser.Tactic in
syntax (name:=gtrans_tac') "gtrans" (config)? (discharger)? (normalizer)? : tactic


open Lean.Parser.Tactic in
syntax (name:=gtrans_conv') "gtrans" (config)? (discharger)? (normalizer)? : conv


declare_config_elab elabGTransConfig  SciLean.Tactic.GTrans.Config

private def emptyDischarge : Expr → MetaM (Option Expr) :=
  fun e =>
    withTraceNode `Meta.Tactic.gtrans
      (fun r => do pure s!"[{ExceptToEmoji.toEmoji r}] discharging: {← ppExpr e}") do
      pure none


-- todo: don't use fun_prop's `tacticToDischarge`
open Lean.Parser.Tactic Mathlib.Meta.FunProp in
private def elabDischarger (disch : Option (TSyntax ``discharger)) : MetaM (Expr → MetaM (Option Expr)) := do
    match disch with
    | none => pure emptyDischarge
    | some d =>
      match d with
      | `(discharger| (discharger:=$tac)) => pure <| tacticToDischarge (← `(tactic| ($tac)))
      | _ => pure emptyDischarge


open Lean.Parser.Tactic Mathlib.Meta.FunProp in
private def elabNormalizer (norm : Option (TSyntax ``normalizer)) : Expr → MetaM Simp.Result :=
    match norm with
    | none => (fun e => pure { expr := e} )
    | some d =>
      match d with
      | `(normalizer| (normalizer:=$c)) =>
         fun e => do
           let ((e',prf),_) ← elabConvRewrite e #[] (← `(conv| ($c))) |>.run {} {}
           return { expr := e', proof? := prf }
      | _ => (fun e => pure { expr := e} )


@[tactic gtrans_tac] unsafe def gtransTac : Tactic := fun _ => do
  let goal ← getMainGoal

  let e ← goal.getType

  let (.some prf, _) ← ((gtrans e).run {}).run {}
    | throwError "gtrans: faild to prove {← ppExpr e}"

  goal.assignIfDefEq prf

@[tactic gtrans_tac'] unsafe def gtransTac' : Tactic
| `(tactic| gtrans $(cfg)? $(disch)? $(norm)?) => do

  let cfg ← match cfg with | .some cfg => elabGTransConfig cfg | .none => pure {}
  let disch ← elabDischarger disch
  let norm := elabNormalizer norm

  let goal ← getMainGoal

  let e ← goal.getType

  let (.some prf, _) ← ((gtrans e).run {config := cfg, discharge := disch, normalize := norm}).run {}
    | throwError "gtrans: faild to prove {← ppExpr e}"

  goal.assignIfDefEq prf
| _ => throwUnsupportedSyntax



@[tactic gtrans_conv] unsafe def gtransConv : Tactic := fun _ => do
  let e ← Conv.getLhs

  let (.some _, _) ← ((gtrans e).run {}).run {}
    | throwError "gtrans: faild to prove {← ppExpr e}"

open Mathlib.Meta.FunProp Lean.Parser.Tactic in
@[tactic gtrans_conv'] unsafe def gtransConv' : Tactic
| `(conv| gtrans $(cfg)? $(disch)? $(norm)?) => do
  let e ← Conv.getLhs

  let cfg ← match cfg with | .some cfg => elabGTransConfig cfg | .none => pure {}
  let disch ← elabDischarger disch
  let norm := elabNormalizer norm

  let (.some _, _) ← ((gtrans e).run {config := cfg, discharge := disch, normalize := norm}).run {}
    | throwError "gtrans: faild to prove {← ppExpr e}"
| _ => throwUnsupportedSyntax


  -- goal.assignIfDefEq prf


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
