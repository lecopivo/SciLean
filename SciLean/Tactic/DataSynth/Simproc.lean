import SciLean.Tactic.DataSynth.Main

namespace SciLean

open Lean Meta

/-- Make simproc out of a theorem of the form `P → x = y` where `P` is `data_synth` goal.

An example of such theorem is:
```
theorem revFDeriv_from_hasRevFDeriv {f f'}
    (hf : HasRevFDeriv K f f') : revFDeriv K f = f' := ...
```

Warning: Currently it is assumed that the `data_synth` goal is the last argument of the theorem!
-/
def mkDataSynthSimproc (simprocName : Name) (thm : Name) : Simp.Simproc := fun e => do
  let thmExpr ← mkConstWithFreshMVarLevels thm
  let thmType ← inferType thmExpr
  let (xs,_,statement) ← forallMetaTelescope thmType

  let .some (_,lhs,rhs) := statement.eq?
    | throwError m!"{simprocName} error: expected equality {statement}!"

  unless ← isDefEq lhs e do
    throwError m!"{simprocName} error: expected expression of the form {lhs}, got {e}!"

  -- extract data_synth goal, for now we expect it is the last argument of the theorem
  let hf := xs[xs.size-1]!
  let hfType ← inferType hf >>= instantiateMVars

  forallTelescope hfType fun ys hfType' => do
  let .some goal ← Tactic.DataSynth.isDataSynthGoal? hfType'
    | throwError m!"{simprocName} error: expected `data_synth` goal, got {hfType} instead!"


  let disch? := (← Simp.getMethods).discharge?
  let state : IO.Ref Tactic.DataSynth.State ← ST.mkRef {}
  -- run data_synth
  let .some r ← Tactic.DataSynth.dataSynth goal { discharge := disch? } (← ST.mkRef {}) state
    | let msgs := (← state.get).msgLog
      logError <| msgs.foldl (init:=m!"failed to transform {e}, potential issues are:")
        (fun s msg => m!"{s}\n{msg}")
      return .continue

  unless ← isDefEq hfType (← mkForallFVars ys r.getSolvedGoal) do
    throwError m!"{simprocName} error: failed to assign data"
  unless ← isDefEq hf (← mkLambdaFVars ys r.proof) do
    throwError m!"{simprocName} error: failed to assign proof"

  let prf := thmExpr.beta xs

  return .visit { expr := rhs, proof? := prf }
