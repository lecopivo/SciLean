import Std.Lean.Parser
import Mathlib.Tactic.NormNum.Core

import SciLean.Lean.Meta.Basic
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

          let _ ←
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


def tryTheorems (thrms : Array SimpTheorem) (discharger : Expr → SimpM (Option Expr)) (e : Expr) : SimpM (Option Simp.Step) := do

  for thm in thrms do
    if let some result ← Meta.Simp.tryTheorem? e thm discharger then
      return Simp.Step.visit result
  return none

set_option linter.unusedVariables false in
def letCase (e : Expr) (ftransName : Name) (ext : FTransExt) (f : Expr) : SimpM (Option Simp.Step) := 
  match f with
  | .lam xName xType (.letE yName yType yValue body _) xBi => do
    let yType  := yType.consumeMData
    let yValue := yValue.consumeMData
    let body  := body.consumeMData
    -- We perform reduction because the type is quite often of the form 
    -- `(fun x => Y) #0` which is just `Y` 
    -- Usually this is caused by the usage of `FunLike`
    let yType := yType.headBeta
    if (yType.hasLooseBVar 0) then
      throwError "dependent type encountered {← ppExpr (Expr.forallE xName xType yType default)}"

    if ¬(yValue.hasLooseBVar 0) then
      let body := body.swapBVars 0 1
      let e' := (.letE yName yType yValue (ext.replaceFTransFun e (.lam xName xType body xBi)) false)
      return .some (.visit { expr := e' })

      -- -- swap lambda and let
      -- let e' ← lambdaLetTelescope f fun xs b => do
      --   let f' ← mkLambdaFVars (#[xs[0]!].append xs[2:]) b
      --   let f'' ← mkLambdaFVars (#[xs[1]!, xs[0]!].append xs[2:]) b
      --   let e'' := ext.replaceFTransFun e f''
      --   trace[Meta.Tactic.ftrans.step] "function f'\n{← ppExpr f'}"
      --   trace[Meta.Tactic.ftrans.step] "function f''\n{← ppExpr f''}"
      --   trace[Meta.Tactic.ftrans.step] "new expr'\n{← ppExpr (ext.replaceFTransFun e f')}"
      --   trace[Meta.Tactic.ftrans.step] "new expr''\n{← ppExpr e''}"
      --   mkLambdaFVars #[xs[1]!] (ext.replaceFTransFun e f')
      -- trace[Meta.Tactic.ftrans.step] "case move let out\n{← ppExpr e'}"
      -- trace[Meta.Tactic.ftrans.step] "let value\n{← ppExpr yValue}"
      -- trace[Meta.Tactic.ftrans.step] "let body\n{← ppExpr body}"
      -- return .some (.visit { expr := e' })

    match (body.hasLooseBVar 0), (body.hasLooseBVar 1) with
    | true, true =>
      trace[Meta.Tactic.ftrans.step] "case let\n{← ppExpr e}"
      let f := Expr.lam xName xType (.lam yName yType body default) xBi
      let g := Expr.lam xName xType yValue default
      ext.letRule e f g

    | true, false => 
      trace[Meta.Tactic.ftrans.step] "case let simple\n{← ppExpr e}"
      let f := Expr.lam yName yType body default
      let g := Expr.lam xName xType yValue default
      ext.compRule e f g

    | false, _ => 
      let f := Expr.lam xName xType (body.lowerLooseBVars 1 1) xBi
      return .some (.visit { expr := ext.replaceFTransFun e f})
  | _ => do
    throwError "Invalid use of {`FTrans.letCase} on function:\n{← ppExpr f}"

/--
  Apply simp theorems marked with `ftrans`
-/
def constAppStep (e : Expr) (ftransName : Name) (ext : FTransExt) (funName : Name) : SimpM (Option Simp.Step) := do

  let candidates ← FTrans.getFTransRules funName ftransName

  if candidates.size = 0 then
    trace[Meta.Tactic.ftrans.step] "no theorems associated to {funName}"

  trace[Meta.Tactic.ftrans.theorems] "applicable theorems: {candidates.map fun c => c.origin.key}"

  tryTheorems candidates ext.discharger e


/-- Function transformation of `fun x => g x₁ ... xₙ` where `g` is a free variable
  
  Arguments `ext, f` are assumed to be the result of `getFTrans? e`
  -/
def fvarAppStep (e : Expr) (ext : FTransExt) (f : Expr) : SimpM (Option Simp.Step) := do

  let (g, h) ← splitLambdaToComp f ext.prodMk ext.prodFst ext.prodSnd

  -- we are agresive with transparency here as we want to deal with type synonyms
  -- the motivation is to handle `ProdLp`
  if (← withTransparency .all <| isDefEq g f) then
    trace[Meta.Tactic.ftrans.step] "trivial case fvar app, nothing to be done\n{← ppExpr e}"
    return none
  else
    trace[Meta.Tactic.ftrans.step] "case fvar app\n{← ppExpr e}\n=\n{g}\n∘\n{h}"
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
      -- aggressively reduce to see through any possible type synonyms
      -- the motivation is to handle `PiLp`
      let xType' ← reduce (skipTypes := false) (← withTransparency TransparencyMode.all <| whnf xType)
      let Lean.Expr.forallE iName iType type bi := xType'
        | trace[Meta.Tactic.ftrans.step] "can't handle this bvar app case, unexpected function type {← ppExpr xType'}"
          return none
      ext.projRule e (.lam iName iType type bi) x
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
def main (e : Expr) : SimpM (Option Simp.Step) := do

  let .some (ftransName, ext, f) ← getFTrans? e
    | return none

  match f.consumeMData with
  | .letE .. => letTelescope f λ xs b => do
    trace[Meta.Tactic.ftrans.step] "case let x := ..; ..\n{← ppExpr e}"
    let e' ← mkLetFVars xs (ext.replaceFTransFun e b)
    return .some (.visit { expr := e' })

  | .lam xName xType xBody xBi => 

    match xBody.consumeMData.headBeta.consumeMData with
    | (.bvar 0) => 
      trace[Meta.Tactic.ftrans.step] "case id\n{← ppExpr e}"
      ext.idRule e xType 

    | .letE yName yType yValue body d => 
      let f' := Expr.lam xName xType (.letE yName yType yValue body d) xBi
      letCase e ftransName ext f'

    | .lam  .. => 
      trace[Meta.Tactic.ftrans.step] "case pi\n{← ppExpr e}"
      ext.piRule e f

    -- | .mvar .. => return .some (.visit  {expr := ← instantiateMVars e})

    | xBody => do
      if !(xBody.hasLooseBVar 0) then
        trace[Meta.Tactic.ftrans.step] "case const\n{← ppExpr e}"
        ext.constRule e xType xBody
      else 
        let f' := Expr.lam xName xType xBody xBi
        let g := xBody.getAppFn'
        match g with 
        | .fvar .. => 
          trace[Meta.Tactic.ftrans.step] "case fvar app `{← ppExpr g}`\n{← ppExpr e}"
          fvarAppStep e ext f'
        | .bvar .. => 
          trace[Meta.Tactic.ftrans.step] "case bvar app\n{← ppExpr e}"
          bvarAppStep e ext f'
        | .const funName _ =>
          trace[Meta.Tactic.ftrans.step] "case const app `{funName}`.\n{← ppExpr e}"
          constAppStep e ftransName ext funName
        -- | .mvar .. => do
        --   return .some (.visit  { expr := ← instantiateMVars e })
        | _ => 
          trace[Meta.Tactic.ftrans.step] "unknown case, app function constructor: {g.ctorName}\n{← ppExpr e}\n"
          return none

  -- | .mvar _ => do
  --   return .some (.visit  {expr :=← instantiateMVars e})

  | f => 
    match f.getAppFn.consumeMData with
    | .const funName _ => 
      trace[Meta.Tactic.ftrans.step] "case const app `{funName}`.\n{← ppExpr e}"
      constAppStep e ftransName ext funName
    | _ => 
      trace[Meta.Tactic.ftrans.step] "unknown case, expression constructor: {f.ctorName}\n{← ppExpr e}\n"
      return none

set_option linter.unusedVariables false in
def tryFTrans? (e : Expr) (discharge? : Expr → SimpM (Option Expr)) (post := false) : SimpM (Option Simp.Step) := do

  if post then
    -- trace[Meta.Tactic.ftrans.step] "post step on:\n{← ppExpr e}"
    return none
  else 
    -- trace[Meta.Tactic.ftrans.step] "pre step on:\n{← ppExpr e}"
    main e

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
