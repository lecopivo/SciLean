import Lean.Elab.Tactic.Conv
import SciLean.Tactic.DataSynth.Main
import SciLean.Tactic.DataSynth.Simproc

namespace SciLean.Tactic.DataSynth

open Lean Meta Elab Tactic

declare_config_elab elabDataSynthConfig Config

open Parser.Tactic in
/-- `date_synth` as conv tactic will fill in meta variables in generalized transformation -/
syntax (name:=data_synth_conv) "data_synth" optConfig (discharger)? : conv


/- syntax (name := simp) "simp" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)? : tactic
 -/


@[tactic data_synth_conv] unsafe def dataSynthConv : Tactic
| `(conv| data_synth $cfg:optConfig $[$disch?]?) => do
  let e ← Conv.getLhs

  let cfg ← elabDataSynthConfig cfg

  let some g ← isDataSynthGoal? e
    | throwError "{e} is not `data_synth` goal"

  let stateRef : IO.Ref DataSynth.State ← IO.mkRef {}

  let disch : Expr → MetaM (Option Expr) :=
    match disch? with
    | none => fun _ => return none
    | some stx => Mathlib.Meta.FunProp.tacticToDischarge ⟨stx.raw[3]⟩

  let simpCtx ← Simp.mkContext (config := cfg.toConfig) (simpTheorems := #[← getSimpTheorems])
  let simpMethods ← Simp.mkDefaultMethods
  let simpStateRef ← ST.mkRef ({} : Simp.State)
  let cacheRef ← ST.mkRef ({} : Std.HashMap ExprStructEq Expr)
  let r? ← dataSynth g
    {config := cfg, discharge := fun e => do disch e}
    cacheRef
    stateRef
    simpMethods.toMethodsRef
    simpCtx
    simpStateRef

  match r? with
  | some r =>
    let e' := r.getSolvedGoal
    if ← isDefEq e e' then
      Conv.changeLhs e'
    else
      throwError "faield to assign data {e'}"
  | none =>
    throwError "`data_synth` failed"
| _ => throwUnsupportedSyntax



open Parser.Tactic Conv in
syntax (name:=data_synth_tac) "data_synth" optConfig (discharger)? ("=>" convSeq)? : tactic

@[tactic data_synth_tac] unsafe def dataSynthTactic : Tactic
| `(tactic| data_synth $cfg:optConfig $[$disch?]? $[=> $c]?) => do
  let m ← getMainGoal
  m.withContext do
  let e ← m.getType

  let cfg ← elabDataSynthConfig cfg

  let some g ← isDataSynthGoal? e
    | throwError "{e} is not `data_synth` goal"

  let disch : Expr → MetaM (Option Expr) :=
    match disch? with
    | none => fun _ => return none
    | some stx => Mathlib.Meta.FunProp.tacticToDischarge ⟨stx.raw[3]⟩

  let stateRef : IO.Ref DataSynth.State ← IO.mkRef {}

  let simpCtx ← Simp.mkContext (config := cfg.toConfig) (simpTheorems := #[← getSimpTheorems])
  let simpMethods ← Simp.mkDefaultMethods
  let simpStateRef ← ST.mkRef ({} : Simp.State)
  let cacheRef ← ST.mkRef ({} : Std.HashMap ExprStructEq Expr)
  let r? ← dataSynth g
    {config := cfg, discharge := fun e => do disch e}
    cacheRef
    stateRef
    simpMethods.toMethodsRef
    simpCtx
    simpStateRef

  match r? with
  | some r =>
    let mut e' := r.getSolvedGoal
    if let some c := c then
      let (e'',eq) ← elabConvRewrite e' #[] (← `(conv| ($c)))
      if ← isDefEq e e'' then
        m.assign (← mkEqMP eq r.proof)
        setGoals []
    else
      if ← isDefEq e e' then
        m.assign r.proof
        setGoals []
      else
        throwError "faield to assign data {e'}"
  | none =>
    throwError "`data_synth` failed"
| _ => throwUnsupportedSyntax
