import Std.Lean.Parser
import Mathlib.Tactic.NormNum.Core

import SciLean.Lean.Meta.Basic
import SciLean.Data.Prod
import SciLean.Tactic.LSimp.Main

import SciLean.Tactic.FTrans.Init

open Lean Meta

namespace SciLean

namespace FTrans

/-

Glossary:

  - function transformation expression - a valied expression that is a function transformation applied to a function
-/

/-- 
  Returns function transformation name and function being tranformed if `e` is function tranformation expression.
 -/
def getFTrans? (e : Expr) : CoreM (Option (Name × Info × Expr)) := do
  let .some ftransName := e.getAppFn.constName?
    | return none

  let .some info ← infoExt.find? ftransName
    | return none

  let .some f := info.getFTransFun? e
    | return none

  return (ftransName, info, f)

/-- 
  Returns function transformation info if `e` is function tranformation expression.
 -/
def getFTransInfo? (e : Expr) : CoreM (Option Info) := do
  let .some (_, info, _) ← getFTrans? e
    | return none
  return info

/-- 
  Returns function transformation info if `e` is function tranformation expression.
 -/
def getFTransFun? (e : Expr) : CoreM (Option Expr) := do
  let .some (_, _, f) ← getFTrans? e
    | return none
  return f


open Elab Term in
def tacticToDischarge (tacticCode : Syntax) : Expr → SimpM (Option Expr) := fun e => do
    let mvar ← mkFreshExprSyntheticOpaqueMVar e `simp.discharger
    let runTac? : TermElabM (Option Expr) :=
      try
        /- We must only save messages and info tree changes. Recall that `simp` uses temporary metavariables (`withNewMCtxDepth`).
           So, we must not save references to them at `Term.State`. -/
        withoutModifyingStateWithInfoAndMessages do
          instantiateMVarDeclMVars mvar.mvarId!
          let goals ←
            withSynthesize (mayPostpone := false) do Tactic.run mvar.mvarId! (Tactic.evalTactic tacticCode *> Tactic.pruneSolvedGoals)
          dbg_trace "number of trailing goals after solving {← ppExpr e} is {goals.length}"

          let result ← instantiateMVars mvar
          if result.hasExprMVar then
            return none
          else
            return some result
      catch _ =>
        return none
    let (result?, _) ← runTac?.run {} {} 
    
    return result?


/--
  Apply simp theorems marked with `ftrans`
-/
def applyTheorems (e : Expr) (discharge? : Expr → SimpM (Option Expr)) : SimpM (Option Simp.Step) := do
  let .some ext ← getSimpExtension? "ftrans_core" | return none
  let thms ← ext.getTheorems

  if let some r ← Simp.rewrite? e thms.pre thms.erased discharge? (tag := "pre") (rflOnly := false) then
    return Simp.Step.visit r
  return Simp.Step.visit { expr := e }

/-- Try to apply function transformation to `e`. Returns `none` if expression is not a function transformation applied to a function.
  -/
def main (e : Expr) (discharge? : Expr → SimpM (Option Expr)) : SimpM (Option Simp.Step) := do

  let .some (ftransName, info, f) ← getFTrans? e
    | return none

  trace[Meta.Tactic.ftrans.step] "{ftransName}\n{← ppExpr e}"

  -- let s ← getThe Simp.State
  -- let c : HashMap _ _ := s.cache
  -- let keys ← c.foldM (fun s k r => do return s ++ s!"  key: {← ppExpr k} | value: {← ppExpr r.expr}\n") ""
  -- trace[Meta.Tactic.ftrans.step] "cache:\n{keys}"


  match f with -- is `f` guaranteed to be in `ldsimp` normal form?
  | .lam _ _ (.letE ..) _ => info.applyLambdaLetRule e
  | .lam _ _ (.lam  ..) _ => info.applyLambdaLambdaRule e
  -- | .lam _ t _ _  => 
  --   if let .some e' ← applyStructureRule
    -- check if `t` is a structure and apply specialized rule for structure projections
  | .letE .. => letTelescope f λ xs b => do
    -- swap all let bindings and the function transformation
    let e' ← mkLetFVars xs (info.replaceFTransFun e b)
    return .some (.visit (.mk e' none 0))
  -- | .lam .. => do
  | _ => do
    applyTheorems e (tacticToDischarge (← liftM info.discharger))
  -- | _ => do
  --   let f' ← etaExpand f
  --   applyTheorems (info.replaceFTransFun e f') (fun e' => info.discharge e')


def tryFTrans? (e : Expr) (discharge? : Expr → SimpM (Option Expr)) (post := false) : SimpM (Option Simp.Step) := do

  if post then
    return none
  else 
    main e discharge?

variable (ctx : Simp.Context) (useSimp := true) in
mutual
  -- This custom discharger is a residue of the code for `norm_num`
  -- It is probably useless and the code can be simplified
  partial def discharge (e : Expr) : SimpM (Option Expr) := do (← deriveSimp e).ofTrue

  partial def methods : Simp.Methods :=
    if useSimp then {
      pre  := fun e ↦ do
        Simp.andThen (← Simp.preDefault e discharge) (fun e' => tryFTrans? e' discharge)
      post := fun e ↦ do
        Simp.andThen (← Simp.postDefault e discharge) (fun e' => tryFTrans? e' discharge (post := true))
      discharge? := discharge
    } else {
      pre  := fun e ↦ Simp.andThen (.visit { expr := e }) (fun e' => tryFTrans? e' discharge)
      post := fun e ↦ Simp.andThen (.visit { expr := e }) (fun e' => tryFTrans? e' discharge (post := true))
      discharge? := discharge
    }

  partial def deriveSimp (e : Expr) : MetaM Simp.Result :=
    (·.1) <$> Tactic.LSimp.main e ctx (methods := methods)
end


-- FIXME: had to inline a bunch of stuff from `simpGoal` here
/--
The core of `norm_num` as a tactic in `MetaM`.

* `g`: The goal to simplify
* `ctx`: The simp context, constructed by `mkSimpContext` and
  containing any additional simp rules we want to use
* `fvarIdsToSimp`: The selected set of hypotheses used in the location argument
* `simplifyTarget`: true if the target is selected in the location argument
* `useSimp`: true if we used `norm_num` instead of `norm_num1`
-/
def fTransAt (g : MVarId) (ctx : Simp.Context) (fvarIdsToSimp : Array FVarId)
    (simplifyTarget := true) (useSimp := true) :
    MetaM (Option (Array FVarId × MVarId)) := g.withContext do
  g.checkNotAssigned `norm_num
  let mut g := g
  let mut toAssert := #[]
  let mut replaced := #[]
  for fvarId in fvarIdsToSimp do
    let localDecl ← fvarId.getDecl
    let type ← instantiateMVars localDecl.type
    let ctx := { ctx with simpTheorems := ctx.simpTheorems.eraseTheorem (.fvar localDecl.fvarId) }
    let r ← deriveSimp ctx useSimp type
    match r.proof? with
    | some _ =>
      let some (value, type) ← applySimpResultToProp g (mkFVar fvarId) type r
        | return none
      toAssert := toAssert.push { userName := localDecl.userName, type, value }
    | none =>
      if r.expr.isConstOf ``False then
        g.assign (← mkFalseElim (← g.getType) (mkFVar fvarId))
        return none
      g ← g.replaceLocalDeclDefEq fvarId r.expr
      replaced := replaced.push fvarId
  if simplifyTarget then
    let res ← g.withContext do
      let target ← instantiateMVars (← g.getType)
      let r ← deriveSimp ctx useSimp target
      let some proof ← r.ofTrue
        | some <$> applySimpResultToTarget g target r
      g.assign proof
      pure none
    let some gNew := res | return none
    g := gNew
  let (fvarIdsNew, gNew) ← g.assertHypotheses toAssert
  let toClear := fvarIdsToSimp.filter fun fvarId ↦ !replaced.contains fvarId
  let gNew ← gNew.tryClearMany toClear
  return some (fvarIdsNew, gNew)

open Qq Lean Meta Elab Tactic Term

/-- Constructs a simp context from the simp argument syntax. -/
def getSimpContext (args : Syntax) (simpOnly := false) :
    TacticM Simp.Context := do
  let simpTheorems ←
    if simpOnly then simpOnlyBuiltins.foldlM (·.addConst ·) {} else getSimpTheorems
  let mut { ctx, starArg } ← elabSimpArgs args (eraseLocal := false) (kind := .simp)
    { simpTheorems := #[simpTheorems], congrTheorems := ← getSimpCongrTheorems }
  unless starArg do return ctx
  let mut simpTheorems := ctx.simpTheorems
  for h in ← getPropHyps do
    unless simpTheorems.isErased (.fvar h) do
      simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
  pure { ctx with simpTheorems }

open Elab.Tactic in

/--
Elaborates a call to `fun_trans only? [args]` or `norm_num1`.
* `args`: the `(simpArgs)?` syntax for simp arguments
* `loc`: the `(location)?` syntax for the optional location argument
* `simpOnly`: true if `only` was used in `norm_num`
* `useSimp`: false if `norm_num1` was used, in which case only the structural parts
  of `simp` will be used, not any of the post-processing that `simp only` does without lemmas
-/
-- FIXME: had to inline a bunch of stuff from `mkSimpContext` and `simpLocation` here
def elabFTrans (args : Syntax) (loc : Syntax)
    (simpOnly := false) (useSimp := true) : TacticM Unit := do
  let ctx ← getSimpContext args (!useSimp || simpOnly)
  let ctx := {ctx with config := {ctx.config with iota := true, zeta := false, singlePass := true}}
  let g ← getMainGoal
  let res ← match expandOptLocation loc with
  | .targets hyps simplifyTarget => fTransAt g ctx (← getFVarIds hyps) simplifyTarget useSimp
  | .wildcard => fTransAt g ctx (← g.getNondepPropHyps) (simplifyTarget := true) useSimp
  match res with
  | none => replaceMainGoal []
  | some (_, g) => replaceMainGoal [g]


open Lean.Parser.Tactic in
elab (name := fTrans) "ftrans" only:&" only"? args:(simpArgs ?) loc:(location ?) : tactic =>
  elabFTrans args loc (simpOnly := only.isSome) (useSimp := true)


open Lean Elab Tactic Lean.Parser.Tactic

syntax (name := fTransConv) "ftrans" &" only"? (simpArgs)? : conv

/-- Elaborator for `norm_num` conv tactic. -/
@[tactic fTransConv] def elabFTransConv : Tactic := fun stx ↦ withMainContext do
  let ctx ← getSimpContext stx[2] !stx[1].isNone
  let ctx := {ctx with config := {ctx.config with iota := true, zeta := false, singlePass := true}}
  Conv.applySimpResult (← deriveSimp ctx (← instantiateMVars (← Conv.getLhs)) (useSimp := true))
