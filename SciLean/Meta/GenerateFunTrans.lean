import SciLean.Tactic.FunTrans.Core
import SciLean.Lean.Meta.Basic
import SciLean.Util.RewriteBy
import SciLean.Meta.GenerateFunProp
import SciLean.Lean.Array

open Lean Meta Elab Term Command Mathlib.Meta

namespace SciLean

initialize registerTraceClass `Meta.Tactic.fun_trans.generate

structure DefineFunTransConfig where
  defineIfSimilarExists := true
  defineNewFunction := true

def levelMVarToParamArray (es : Array Expr) : MetaM (Array Expr × Array Name) := do
  let e ← es.joinrM pure (fun x y => mkAppM ``PProd.mk #[x,y])
  let (e,_) ← (levelMVarToParam e).run {}
  let lvls := (collectLevelParams {} e).params

  let mut e := e
  let mut es := #[]
  while e.isAppOf ``PProd.mk do
    es := es.push e.appFn!.appArg!
    e := e.appArg!
  es := es.push e
  return (es,lvls)

open FunTrans
def generateFunTransDefAndTheorem (statement proof : Expr) (ctx : Array Expr)
    (suffix : Option Name := none) (cfg : DefineFunTransConfig := {}) :
    MetaM Bool := do

  let .some (_,lhs,rhs) := statement.eq?
    | throwError s!"equality expected, got {← ppExpr statement}"

  let .some (funTransDecl, f) ← Mathlib.Meta.FunTrans.getFunTrans? lhs
    | throwError s!"unrecognized function transformation {← ppExpr lhs}!"

  let .data fData ← FunProp.getFunctionData? f FunProp.defaultUnfoldPred {zeta:=false}
    | throwError s!"invalid function {← ppExpr f}"

  let .some funName ← fData.getFnConstName?
    | throwError s!"invalid function {← ppExpr f}"

  let argNames ← getConstArgNames funName true
  let argNames := fData.mainArgs.map (fun i => argNames[i]!)

  let similarTheorems ←
      getTheoremsForFunction funName funTransDecl.funTransName fData.args.size fData.mainArgs
  if similarTheorems.size ≠ 0 then
    unless cfg.defineIfSimilarExists do
      trace[Meta.Tactic.fun_trans.generate]
        "not generating `fun_trans` theorem for {statement} because similar theorems exist:
         {similarTheorems.map (fun t => t.thmOrigin.name)}"
      return false


  trace[Meta.Tactic.fun_trans.generate] "
     Generating `fun_trans` theorem for `{statement}`
     Function name:  {funName}
     Function trans: {funTransDecl.funTransName}
     Arguments:      {argNames}"

  let declSuffix := argNames.foldl (init := "arg_") (fun s n => s ++ toString n)

  let defName := funName.append (.mkSimple declSuffix)
    |>.append (.mkSimple funTransDecl.funTransName.lastComponentAsString)
  let defName := if let .some s := suffix then defName.appendAfter (toString s) else defName
  let defCtx  := ctx.filter (fun x => rhs.containsFVar x.fvarId!)
  let defVal  ← mkLambdaFVars defCtx rhs >>= instantiateMVars

  -- turn level mvars to params
  let (defVal',lvls) ← levelMVarToParamArray #[defVal]
  let defVal := defVal'[0]!

  let decl : DefinitionVal :=
  {
    name  := defName
    type  := ← inferType defVal
    value := defVal
    hints := .regular 0
    safety := .safe
    levelParams := lvls.toList
  }

  if cfg.defineNewFunction then
    addDecl (.defnDecl decl)
    try
      compileDecl (.defnDecl decl)
    catch _ =>
      trace[Meta.Tactic.fun_trans.generate] "failed to complie {defName}!"

  let thmName := defName.appendAfter "_rule"
  let thmName := if let .some s := suffix then thmName.appendAfter (toString s) else thmName
  let thmCtx := ctx.filter (fun x => proof.containsFVar x.fvarId!)
  let thmType ←
    if cfg.defineNewFunction then
      mkForallFVars thmCtx (← mkEq lhs (← mkAppOptM defName (defCtx.map some)))
    else
      mkForallFVars thmCtx statement
    >>= instantiateMVars
  let thmVal  ← mkLambdaFVars thmCtx proof >>= instantiateMVars

  let thmDecl : TheoremVal :=
  {
    name  := thmName
    type  := ← instantiateMVars thmType
    value := ← instantiateMVars thmVal
    levelParams := lvls.toList
  }

  IO.println (← ppExpr thmType)
  IO.println (← ppExpr thmVal)

  addDecl (.thmDecl thmDecl)
  FunTrans.addTheorem thmName

  return true


/--
Given a proof of function property `proof` like `q(by fun_prop : Differentiable Real.sin)`
generate theorems for all the function transformations that follow from this. -/
partial def defineTransitiveFunTransFromFunProp (proof : Expr) (ctx : Array Expr)
    (suffix : Option Name := none) : MetaM Unit := do
  trace[Meta.Tactic.fun_prop.generate] "generating transformations from `{← inferType proof}`"
  let s := FunTrans.fvarTheoremsExt.getState (← getEnv)

  s.theorems.forValuesM fun thm => do
    trace[Meta.Tactic.fun_prop.generate]
      "trying transition theorem {← ppOrigin (Origin.decl thm.thmName)}"
    let thmProof ← mkConstWithFreshMVarLevels thm.thmName
    let thmType ← inferType thmProof
    let (xs,_,thmType) ← forallMetaTelescope thmType
    let thmProof := mkAppN thmProof xs

    for x in xs do

      if (← isDefEq x proof) then
        let thmProof ← instantiateMVars thmProof
        let thmType ← instantiateMVars thmType

        -- filer out assigned mvars
        let xs' ← xs.filterM (m:=MetaM) (fun x => do pure (← instantiateMVars x).hasMVar)

        -- turn mvars to fvars
        let thmProof ← mkLambdaFVars xs' thmProof
        let thmType ← mkForallFVars xs' thmType
        forallTelescope thmType fun xs'' thmType => do

          let _ ← generateFunTransDefAndTheorem thmType (thmProof.beta xs'') (ctx++xs'')
                     suffix {defineIfSimilarExists := false, defineNewFunction := false }


open Mathlib.Meta
/-- Define function transformation, the command
-/
elab  "def_fun_trans" _doTrans:("with_transitive")? suffix:(ident)? bs:bracketedBinder* ":" e:term "by" c:Lean.Parser.Tactic.Conv.convSeq : command => do

  runTermElabM fun ctx₁ => do
    elabBinders bs fun ctx₂ => do
    let e ← elabTermAndSynthesize (← `($e)) none
    let e := e.headBeta.eta
    let (e',prf) ← elabConvRewrite e #[] (← `(conv| ($c)))
    let suffix := suffix.map (·.getId)
    let _ ← generateFunTransDefAndTheorem (← mkEq e e') prf (ctx₁++ctx₂) suffix


open Mathlib.Meta
elab  "abbrev_fun_trans" _doTrans:("with_transitive")? suffix:(ident)? bs:bracketedBinder* ":" e:term "by" c:Lean.Parser.Tactic.Conv.convSeq : command => do

  runTermElabM fun ctx₁ => do
    elabBinders bs fun ctx₂ => do
    let e ← elabTermAndSynthesize (← `($e)) none
    let e := e.headBeta.eta
    let (e',prf) ← elabConvRewrite e #[] (← `(conv| ($c)))
    let suffix := suffix.map (·.getId)
    let _ ← generateFunTransDefAndTheorem (← mkEq e e') prf (ctx₁++ctx₂) suffix { defineNewFunction := false }
