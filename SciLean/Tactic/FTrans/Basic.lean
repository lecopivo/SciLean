import Std.Lean.Parser
import Mathlib.Tactic.NormNum.Core

import SciLean.Lean.Meta.Basic
import SciLean.Data.Prod
import SciLean.Tactic.LSimp.Main

import SciLean.Tactic.FTrans.Init

open Lean Meta

namespace SciLean.FTrans


open Elab Term in
def tacticToDischarge (tacticCode : Syntax) : Expr → MetaM (Option Expr) := fun e => do
    let mvar ← mkFreshExprSyntheticOpaqueMVar e `simp.discharger
    let runTac? : TermElabM (Option Expr) :=
      try
        /- We must only save messages and info tree changes. Recall that `simp` uses temporary metavariables (`withNewMCtxDepth`).
           So, we must not save references to them at `Term.State`. -/
        withoutModifyingStateWithInfoAndMessages do
          instantiateMVarDeclMVars mvar.mvarId!

          let goals ←
            withSynthesize (mayPostpone := false) do Tactic.run mvar.mvarId! (Tactic.evalTactic tacticCode *> Tactic.pruneSolvedGoals)

          let result ← instantiateMVars mvar
          if result.hasExprMVar then
            return none
          else
            return some result
      catch _ =>
        return none
    let (result?, _) ← runTac?.run {} {} 
    
    return result?


def tryNamedTheorem (thrm : Name) (discharger : Expr → SimpM (Option Expr)) (e : Expr) : SimpM (Option Simp.Step) := do

  let thm : SimpTheorem := {
    proof := mkConst thrm
    origin := .decl thrm
    rfl := false
  }

  let .some result ← Meta.Simp.tryTheorem? e thm discharger
    | return none
  return .some (.visit result)


/--
  Apply simp theorems marked with `ftrans`
-/
def applyTheorems (e : Expr) (ftransName : Name) (ext : FTransExt) (f : Expr) : SimpM (Option Simp.Step) := do

  let .some funName ← getFunHeadConst? f
    | return none

  let candidates ← FTrans.getFTransRules funName ftransName

  for thm in candidates do
    if let some result ← Meta.Simp.tryTheorem? e thm ext.discharger then
      return Simp.Step.visit result
  return none


/-- Function transformation of `fun x => g x₁ ... xₙ` where `g` is a free variable
  
  Arguments `ext, f` are assumed to be the result of `getFTrans? e`
  -/
def fvarAppStep (e : Expr) (ext : FTransExt) (f : Expr) : SimpM (Option Simp.Step) := do

  let (g, h) ← splitLambdaToComp f

  -- trivial case? 
  if (← isDefEq g f ) then
    trace[Meta.Tactic.ftrans.step] "trivial case fvar app, nothing to be done\n{← ppExpr e}"
    return none
  else
    trace[Meta.Tactic.ftrans.step] "case fvar app\n{← ppExpr e}"
    ext.compRule e g h


/-- Function transformation of `fun x => g x₁ ... xₙ` where `g` is a bound variable
  
  Arguments `ext, f` are assumed to be the result of `getFTrans? e`
  -/
def bvarAppStep (e : Expr) (ext : FTransExt) (f : Expr) : SimpM (Option Simp.Step) := do

  match f with

  | .lam xName xType (.app g x) bi =>
    if x.hasLooseBVars then
      trace[Meta.Tactic.ftrans.step] "can't handle this bvar app case, unexpected dependency in argument {← ppExpr (.lam xName xType x bi)}"
      return none

    if g == (.bvar 0) then
      ext.projRule e
    else
      let gType := (← inferType (.lam xName xType g bi)).getForallBody
      if gType.hasLooseBVars then
        trace[Meta.Tactic.ftrans.step] "can't handle this bvar app case, unexpected dependency in type of {← ppExpr (.lam xName xType g bi)}"
        return none

      let h₁ := Expr.lam (xName.appendAfter "'") gType ((Expr.bvar 0).app x) bi
      let h₂ := Expr.lam xName xType g bi 
      ext.compRule e h₁ h₂

  | _ => return none


/-- Try to apply function transformation to `e`. Returns `none` if expression is not a function transformation applied to a function.
  -/
def main (e : Expr) (discharge? : Expr → SimpM (Option Expr)) : SimpM (Option Simp.Step) := do

  let .some (ftransName, ext, f) ← getFTrans? e
    | return none


  match f with
  | .letE .. => letTelescope f λ xs b => do
    trace[Meta.Tactic.ftrans.step] "case let\n{← ppExpr e}"
    let e' ← mkLetFVars xs (ext.replaceFTransFun e b)
    return .some (.visit { expr := e' })

  | .lam _ _ (.bvar  0) _ => 
    trace[Meta.Tactic.ftrans.step] "case id\n{← ppExpr e}"
    ext.idRule e

  | .lam xName xType (.letE yName yType yValue body _) xBi => 
      -- quite often the type looks like `(fun _ => X) x` as residue from `FunLike.coe`
      -- thus we do beta reduction
      let yType := yType.headBeta
      match (body.hasLooseBVar 0), (body.hasLooseBVar 1) with
      | true, true =>
        trace[Meta.Tactic.ftrans.step] "case let\n{← ppExpr e}"
        let f := Expr.lam xName xType (.lam yName yType body default) xBi
        let g := Expr.lam xName xType yValue default
        ext.letRule e f g

      | true, false => 
        trace[Meta.Tactic.ftrans.step] "case comp\n{← ppExpr e}"
        if (yType.hasLooseBVar 0) then
          trace[Meta.Tactic.ftrans.step] "can't handle dependent type {← ppExpr (Expr.forallE xName xType yType default)}"
          return none

        let f := Expr.lam yName yType body default
        let g := Expr.lam xName xType yValue default
        ext.compRule e f g

      | false, _ => 
        let f := Expr.lam xName xType (body.lowerLooseBVars 1 1) xBi
        return .some (.visit { expr := ext.replaceFTransFun e f })

  | .lam _ _ (.lam  ..) _ => 
    trace[Meta.Tactic.ftrans.step] "case pi\n{← ppExpr e}"
    ext.piRule e f

  | .lam _ _ b _ => do
    if !(b.hasLooseBVar 0) then
      trace[Meta.Tactic.ftrans.step] "case const\n{← ppExpr e}"
      ext.constRule e
    else if b.getAppFn.isFVar then
      fvarAppStep e ext f
    else if b.getAppFn.isBVar then
      trace[Meta.Tactic.ftrans.step] "case bvar app\n{← ppExpr e}"
      bvarAppStep e ext f
    else
      trace[Meta.Tactic.ftrans.step] "case theorems\n{← ppExpr e}\n"
      applyTheorems e ftransName ext f

  | _ => do
    applyTheorems e ftransName ext f


def tryFTrans? (e : Expr) (discharge? : Expr → SimpM (Option Expr)) (post := false) : SimpM (Option Simp.Step) := do

  if post then
    -- trace[Meta.Tactic.ftrans.step] "post step on:\n{← ppExpr e}"
    return none
  else 
    -- trace[Meta.Tactic.ftrans.step] "pre step on:\n{← ppExpr e}"
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
      pre  := fun e ↦ do 
        Simp.andThen (.visit { expr := e }) (fun e' => tryFTrans? e' discharge)
      post := fun e ↦ do
        Simp.andThen (.visit { expr := e }) (fun e' => tryFTrans? e' discharge (post := true))
      discharge? := discharge
    }

  partial def deriveSimp (e : Expr) : MetaM Simp.Result := do
    withTraceNode `ftrans (fun _ => return s!"ftrans of {← ppExpr e}") do
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
