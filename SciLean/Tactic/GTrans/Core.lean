import Lean
import Mathlib.Tactic.FunProp

import SciLean.Tactic.GTrans.Decl
import SciLean.Tactic.GTrans.Theorems

import SciLean.Tactic.LetNormalize2

import SciLean.Lean.ToSSA

open Lean Meta Qq
open Mathlib.Meta.FunProp


namespace SciLean.Tactic.GTrans


----------------------------------------------------------------------------------------------------


structure Config where
  maxNumSteps := 100


structure Context where
  config : Config := {}
  normalize : Expr → MetaM Simp.Result := fun e => return { expr := e}
  discharge : Expr → MetaM (Option Expr) := fun _ => return .none


structure State where
  numSteps := 0


abbrev GTransM := ReaderT Context $ StateRefT State MetaM

----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

private def ppExprWithType (e : Expr) : MetaM String := do
  return s!"{← ppExpr e} : {← ppExpr (← inferType e)}"


def defaultNormalize (e : Expr) : MetaM (Expr × Option Expr) := do
  trace[Meta.Tactic.gtrans.normalize] "normalizing {e}"
  -- let e ← whnfCore e {zeta:=false,zetaDelta:=false}
  -- let e ← e.toSSA #[]
  let e ← e.liftLets2 mkLambdaFVars (config:={pullLetOutOfLambda:=false})
  trace[Meta.Tactic.gtrans.normalize] "normalized {e}"
  return (e,none)

def increaseNumSteps : GTransM Unit :=
  modify (fun s => {s with numSteps := s.numSteps + 1 })

def normalize (e : Expr) : GTransM Simp.Result := do (← read).normalize e
def dnormalize (e : Expr) : GTransM Expr := pure e
def discharge? (e : Expr) : GTransM (Option Expr) := do (← read).discharge e

unsafe def synthesizeArgument (x : Expr) (gtrans : Expr → GTransM (Option Expr)) :
    GTransM Bool := do

  let x ← instantiateMVars x
  let X ← inferType x

  unless x.isMVar do return true

  withTraceNode
    `Meta.Tactic.gtrans.arg
    (fun r => do pure s!"[{ExceptToEmoji.toEmoji r}] synthesizing argument {← ppExprWithType x}") do

    if let .some _ ← isGTrans? X then
      if let .some prf ← do gtrans X then
        x.mvarId!.assignIfDefEq prf
        return true
      try
        x.mvarId!.assumption
        return true
      catch _ =>
        pure ()

    if let .some _ ← isClass? X then
      try
        let inst ← synthInstance X
        x.mvarId!.assignIfDefEq inst
        return true
      catch _ =>
        return false

    if X.isAppOfArity ``autoParam 2 then
      let tactic ← Meta.evalExpr (TSyntax `tactic) q(Lean.Syntax) X.appArg!
      trace[Meta.Tactic.gtrans.arg] s!"auto arg tactic {tactic.raw.prettyPrint}"
      let .some prf ← tacticToDischarge ⟨tactic⟩ X.appFn!.appArg! | return false
      if ← isDefEq (← inferType prf) X then
        x.mvarId!.assignIfDefEq prf
        return true

    if let .some prf ← discharge? X then
      if ← isDefEq (← inferType prf) X then
        x.mvarId!.assignIfDefEq prf
        return true

    return false


/-- Replace n-th and all subsequent arguments in `e` with fresh metavariables. -/
def mkTrailingArgsToFreshMVars (e : Expr) (n : ℕ) : MetaM Expr := do
  e.withApp fun fn args => do
    let e' := mkAppN fn args[0:n]
    let (xs, _, _) ← forallMetaTelescope (← inferType e')
    return mkAppN e' xs



unsafe def tryTheorem? (e : Expr) (thm : GTransTheorem) (minOutParam : ℕ)
    (gtrans : Expr → GTransM (Option Expr)) : GTransM (Option Expr) := do

  trace[Meta.Tactic.gtrans] "goal {← ppExpr e}"

  let thmProof ← thm.getProof
  let type ← inferType thmProof
  let (xs, _, type) ← forallMetaTelescope type
  let thmProof := thmProof.beta xs

  trace[Meta.Tactic.gtrans.unify] "unify\n{e}\n=?=\n{type}"

  -- replace all output arguments in `e` with fresh mvars
  let e' ← mkTrailingArgsToFreshMVars e minOutParam
  unless (← isDefEq e' type) do
    trace[Meta.Tactic.gtrans.unify] "unification failed"
    return none

  for x in xs do
    let _ ← synthesizeArgument x gtrans

  -- todo: keep on synthesizing arguments while there is some progress
  for x in xs do
    let _ ← synthesizeArgument x gtrans

  for x in xs do
    let x ← instantiateMVars x
    if x.hasMVar then
      trace[Meta.Tactic.gtrans] "failed to synthesize argument {← ppExprWithType x}"
      return none

  return some thmProof

-- rip off Lean.Meta.Simp.congrArgs
open Simp
def congrNormalize (e : Expr) (args : Array Expr) : GTransM Simp.Result := do
  let mut r : Simp.Result := { expr := e }
  if args.isEmpty then
    return r
  else
    let infos := (← getFunInfoNArgs r.expr args.size).paramInfo
    let mut i := 0
    for arg in args do
      if h : i < infos.size then
        trace[Debug.Meta.Tactic.simp] "app [{i}] {infos.size} {arg} hasFwdDeps: {infos[i].hasFwdDeps}"
        let info := infos[i]
        if !info.hasFwdDeps then
          r ← mkCongr r (← normalize arg)
        else if (← whnfD (← inferType r.expr)).isArrow then
          r ← mkCongr r (← normalize arg)
        else
          r ← mkCongrFun r (← dnormalize arg)
      else if (← whnfD (← inferType r.expr)).isArrow then
        r ← mkCongr r (← normalize arg)
      else
        r ← mkCongrFun r (← dnormalize arg)
      i := i + 1
    return r



/-- `gtrans` accespt expression `e` that has to be of type `Prop` and application of registered
generalized transformation. The goal of `gtrans` is to fill in metavariables in `e` and provide
proof of the resulting proposition.

Meta variables in `e` can appear only in particular places. Each generalize transformation is
expected to have some arguments marked as `outParam` and only these arguments can be metavariables.

Examples:

- `simp` as generalized transformation
  calling `gtrans q(0+n+0 = ?m)` will call simp on `0+n+0` and assign the result to `?m`

- computing derivatives
  calling `gtrans q(HasFDeriv (fun x : ℝ => x*x) ?f' x` will compute derivative
  `?f := fun dx ↦L[K] 2*dx`
 -/
unsafe def gtrans (e : Expr) : GTransM (Option Expr) := do

  forallTelescope e fun _ e => do
  Meta.letTelescope e fun _ e => do

  if (← get).numSteps ≥ (← read).config.maxNumSteps then
    throwError "expected application of generalized transformation, got {← ppExpr e}"
    return none
  increaseNumSteps

  let .some gtransDecl ← isGTrans? e
    | throwError "expected application of generalized transformation, got {← ppExpr e}"

  let ext := gtransTheoremsExt.getState (← getEnv)
  let thms ← ext.theorems.getMatchWithScore e false
  let thms := thms |>.map (·.1) |>.flatten |>.qsort (fun x y => x.priority > y.priority)

  withTraceNode `Meta.Tactic.gtrans (fun r => do pure s!"[{ExceptToEmoji.toEmoji r}] {← ppExpr e}") do

  let keys := ← RefinedDiscrTree.mkDTExprs e false
  trace[Meta.Tactic.gtrans.candidates] "look up key: {keys}"
  trace[Meta.Tactic.gtrans.candidates] "candidates: {thms.map (·.thmName)}"

  let minOutArg := gtransDecl.outputArgs.getMax? (·>·) |>.getD 0

  for thm in thms do
    if let .some prf ←
      withTraceNode `Meta.Tactic.gtrans
        (fun r => do pure s!"[{ExceptToEmoji.toEmoji r}] applying {thm.thmName}") do
        tryTheorem? e thm minOutArg gtrans then

      let e' ← inferType prf

      -- get output arguments and normalize them
      let outArgsNum := e.getAppNumArgs' + 1 - minOutArg
      let r ← congrNormalize (e'.stripArgsN outArgsNum) (e'.getAppArgsN outArgsNum)
        if ← isDefEq e r.expr then
          return ← mkAppM ``Eq.mp #[← r.getProof, prf]
        else
          trace[Meta.Tactic.gtrans] "failed to assign {← ppExpr r.expr} to {← ppExpr e}"

  return none

  -- check if `e` is application of generalized transformation



initialize registerTraceClass `Meta.Tactic.gtrans.candidates
initialize registerTraceClass `Meta.Tactic.gtrans.normalize
initialize registerTraceClass `Meta.Tactic.gtrans.unify
initialize registerTraceClass `Meta.Tactic.gtrans.arg
initialize registerTraceClass `Meta.Tactic.gtrans
