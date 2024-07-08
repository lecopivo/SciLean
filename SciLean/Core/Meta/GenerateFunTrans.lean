import SciLean.Tactic.FunTrans.Core
import SciLean.Lean.Meta.Basic
import SciLean.Util.RewriteBy

open Lean Meta Elab Term Command

namespace SciLean

initialize registerTraceClass `Meta.Tactic.fun_trans.generate

open Mathlib.Meta in
def generateFunTransDefAndTheorem (e : Expr) (ctx : Array Expr) (c : TSyntax `conv) : TermElabM Unit := do

    let .some (funTransDecl, f) ← Mathlib.Meta.FunTrans.getFunTrans? e
      | throwError s!"unrecognized function transformation {← ppExpr e}!"

    let .data fData ← FunProp.getFunctionData? f FunProp.defaultUnfoldPred {zeta:=false}
      | throwError s!"invalid function {← ppExpr f}"

    let .some funName ← fData.getFnConstName?
      | throwError s!"invalid function {← ppExpr f}"

    let argNames ← getConstArgNames funName true
    let argNames := fData.mainArgs.map (fun i => argNames[i]!)

    trace[Meta.Tactic.fun_trans.generate] "
       Generating `fun_trans` theorem for `{e}`
       Function name:  {funName}
       Function trans: {funTransDecl.funTransName}
       Arguments:      {argNames}"

    let (e',prf) ← elabConvRewrite e #[] c

    trace[Meta.Tactic.fun_trans.generate] "
      Transformed by `{Syntax.prettyPrint c}`
      {e}
      ==>
      {e'}"

    let declSuffix := argNames.foldl (init := "arg_") (fun s n => s ++ toString n)


    let defName := funName.append (.mkSimple declSuffix)
      |>.append (.mkSimple funTransDecl.funTransName.lastComponentAsString)
    let defCtx  := ctx.filter (fun x => e'.containsFVar x.fvarId!)
    let defVal  ← mkLambdaFVars defCtx e' >>= instantiateMVars

    -- temporarily change the generated name
    let defName := defName.append `temp

    -- how do I extract all level parameters?
    if defVal.hasLevelParam then
      throwError "value {← ppExpr defVal} has level parameters!"

    let decl : DefinitionVal :=
    {
      name  := defName
      type  := ← inferType defVal
      value := defVal
      hints := .regular 0
      safety := .safe
      levelParams := []
    }

    addDecl (.defnDecl decl)
    try
      compileDecl (.defnDecl decl)
    catch _ =>
      trace[Meta.Tactic.fun_trans.generate] "failed to complie {defName}!"

    let thmName := defName.appendAfter "_rule"
    let thmCtx := ctx.filter (fun x => prf.containsFVar x.fvarId!)
    let thmType ← mkForallFVars thmCtx (← mkEq e (← mkAppOptM defName (defCtx.map some)))
      >>= instantiateMVars
    let thmVal  ← mkLambdaFVars thmCtx prf >>= instantiateMVars

    if thmType.hasLevelParam then
      throwError "theorem statement {← ppExpr thmType} has level parameters!"
    if thmVal.hasLevelParam then
      throwError "theorem proof {← ppExpr thmVal} has level parameters!"

    let thmDecl : TheoremVal :=
    {
      name  := thmName
      type  := thmType
      value := thmVal
      levelParams := []
    }

    addDecl (.thmDecl thmDecl)
    FunTrans.addTheorem thmName


open Mathlib.Meta
elab  "#generate_fun_trans" e:term "by" c:Lean.Parser.Tactic.Conv.convSeq : command => do

  runTermElabM fun ctx => do
    let e ← elabTermAndSynthesize (← `($e)) none
    let e := e.headBeta.eta
    generateFunTransDefAndTheorem e ctx (← `(conv| ($c)))
