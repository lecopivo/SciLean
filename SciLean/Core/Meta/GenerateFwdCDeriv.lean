import SciLean.Core.Meta.GenerateBasic
import SciLean.Core.Meta.ExtendContext
import SciLean.Core.Meta.ParametrizeFVars
import SciLean.Tactic.LetNormalize
import SciLean.Tactic.AnalyzeConstLambda
import SciLean.Lean.Name

open Lean Meta Qq
open Lean Elab Term Lean.Parser.Tactic

namespace SciLean.Meta

open GenerateProperty

def generateFwdCDeriv (constName : Name) (mainNames trailingNames : Array Name) 
  (tac : TSyntax ``tacticSeq) (conv : TSyntax `conv) 
  (extraBinders : Array Syntax) : TermElabM Unit := do
  let info ← getConstInfoDefn constName

  forallTelescope info.type fun xs type => do
  elabBinders extraBinders fun extraCtx => do

    let (ctx, args) ← splitToCtxAndArgs xs
    
    let .some ⟨_u,K,_isROrC⟩ ← getFieldOutOfContextQ (xs++extraCtx)
      | throwError "unable to figure out what is the field"

    trace[Meta.generate_ftrans] "detected field {← ppExpr K}"

    let (mainArgs, unusedArgs, trailingArgs, argKinds) 
      ← splitArgs args mainNames trailingNames

    let type ← mkForallFVars trailingArgs type

    -- ensure that `mainNames` are in the right order
    let mainNames ← mainArgs.mapM (fun arg => arg.fvarId!.getUserName)
  
    let lvls := info.levelParams.map fun p => Level.param p
    let lhsExpr := mkAppN (Expr.const constName lvls) xs
    let rhsExpr ←
      Meta.withLetDecls mainNames mainArgs fun mainArgs' => do
        let xs' := ctx ++ mergeArgs mainArgs' unusedArgs trailingArgs argKinds
        let body := (mkAppN (Expr.const constName lvls) xs').headBeta
        mkLambdaFVars mainArgs' body

    let mainTypes ← liftM <| mainArgs.mapM inferType
    withVecs K (mainTypes.push type) fun vecInsts => do

    let vLvlName := mkUnusedName info.levelParams `w
    let v := Level.param vLvlName
    let lvlParams := vLvlName :: info.levelParams
    withLocalDecl `W .implicit (mkSort v.succ) fun W => do
    withVec K W fun instW => do
    withLocalDecl `w .default W fun w => do

    withParametrizedFVars w mainArgs #[lhsExpr, rhsExpr] fun _ lhsrhs => do

    let decls :=
      mkLocalDecls (n:=TermElabM)
        (mainNames.map (fun n => n.appendBefore "h")) 
        .default
        (← mainArgs.mapM (fun arg => do 
          lambdaTelescope (← etaExpand arg) fun xs b => do
            let f := (← mkLambdaFVars #[xs[0]!] b).eta
            let prop ← mkAppM ``IsDifferentiable #[K,f]
            mkForallFVars xs[1:] prop))

    withLocalDecls decls fun mainArgProps => do

      let f ← mkLambdaFVars (#[w]++trailingArgs) lhsrhs[0]!

      let lhs ← mkAppM ``fwdCDeriv #[K, f]

      let rhs ← mkLambdaFVars (#[w]++trailingArgs) lhsrhs[1]!
      let rhs ← mkAppM ``fwdCDeriv #[K, rhs]

      let isDiff ← mkAppM ``IsDifferentiable #[K, f]

      let (rhs, proof) ← elabConvRewrite rhs conv
      let isDiffProof ← elabProof isDiff tac
    
      -- let .lam _ _ (.lam _ _ rhsBody _) _ := rhs
      --   | throwError "unexpected result after function transformation, expecting `fun w dw => ...` but got\n{←ppExpr rhs}"

      withLocalDecl `dw .default W fun dw => do
      let rhsBody := (mkAppN rhs #[w,dw]).headBeta -- rhsBody.instantiate #[dw,w]
      let dargs ← mainArgs.mapM (fun arg => mkAppM ``fwdCDeriv #[K,arg,w,dw])

      let fwdDerivFun ← 
        withLocalDecls' mainNames .default mainTypes fun ys =>
        let names := mainNames.map (fun n => n.appendBefore "d")
        withLocalDecls' names .default mainTypes fun dys => do
          let dargs' ← ys.mapIdxM (fun i y => mkAppM ``Prod.mk #[y,dys[i]!])
          let rhsBody' ← rhsBody.replaceExprs dargs dargs' 
          let rhsBody' ← LetNormalize.letNormalize rhsBody' {}

          if rhsBody'.containsFVar w.fvarId! then
            throwError "failed to eliminate auxiliary variable `{← ppExpr w}` from\n{← ppExpr rhsBody'}"
          if rhsBody'.containsFVar dw.fvarId! then
            throwError "failed to eliminate auxiliary variable `{← ppExpr dw}` from\n{← ppExpr rhsBody'}"

          let args := ctx ++ vecInsts ++ mergeArgs' ys unusedArgs argKinds ++ dys
          let fwdDerivFun ← mkLambdaFVars args rhsBody' >>= instantiateMVars
          pure fwdDerivFun

      -- calling `analyzeConstLambda` here is bit of an overkill as we are only
      -- interested in `declSuffix`
      let lhsData ← analyzeConstLambda f

      let fwdDerivFunName := 
        constName.append lhsData.declSuffix |>.append "fwdCDeriv"
      let ruleName := fwdDerivFunName.appendAfter "_rule"
      let ruleWithDefName := fwdDerivFunName.appendAfter "_rule_def"
      let isDiffRuleName := 
        constName.append lhsData.declSuffix |>.append "IsDifferentiable_rule"

      let xs' := ctx ++ extraCtx ++ #[W] ++ instW ++ vecInsts ++ mergeArgs' mainArgs unusedArgs argKinds ++ mainArgProps
      let isDiffRule ← mkForallFVars xs' isDiff >>= instantiateMVars
      let isDiffProof ← mkLambdaFVars xs' isDiffProof >>= instantiateMVars

      let isDiffInfo : TheoremVal := 
      {
        name  := isDiffRuleName
        type  := isDiffRule
        value := isDiffProof
        levelParams := lvlParams
      }

      addDecl (.thmDecl isDiffInfo)
      FProp.funTransRuleAttr.attr.add isDiffRuleName (← `(attr|fprop)) .global

      let rule ← mkForallFVars xs' (← mkEq lhs rhs)  >>= instantiateMVars
      let proof ← mkLambdaFVars xs' proof  >>= instantiateMVars

      let ruleInfo : TheoremVal := 
      {
        name  := ruleName
        type  := rule
        value := proof
        levelParams := lvlParams
      }

      addDecl (.thmDecl ruleInfo)

      let fwdDerivFunInfo : DefinitionVal := 
      {
        name  := fwdDerivFunName
        type  := (← inferType fwdDerivFun)
        value := fwdDerivFun
        hints := .regular 0
        safety := .safe
        levelParams := info.levelParams
      }

      addDecl (.defnDecl fwdDerivFunInfo)
      try 
        compileDecl (.defnDecl fwdDerivFunInfo)
      catch _ =>
        trace[Meta.generate_ftrans] "failed to compile declaration {fwdDerivFunName}"

      let rhsWithDef ← do
        let names := mainNames.map (fun n => Name.mkSimple s!"{n}d{n}")
        withLetDecls names dargs fun ydys => do
          let ys ← ydys.mapM (fun ydy => mkAppM ``Prod.fst #[ydy])
          let dys ← ydys.mapM (fun ydy => mkAppM ``Prod.snd #[ydy])
          let args := ctx ++ vecInsts ++ mergeArgs' ys unusedArgs argKinds ++ dys
          let lvls := info.levelParams.map (fun p => Level.param p)
          let body := (mkAppN (.const fwdDerivFunName lvls) args)
          mkLambdaFVars (#[w,dw] ++ ydys) body

      let ruleWithDef ← mkForallFVars xs' (← mkEq lhs rhsWithDef) >>= instantiateMVars

      let ruleWithDefInfo : TheoremVal := 
      {
        name  := ruleWithDefName
        type  := ruleWithDef
        value := proof
        levelParams := lvlParams
      }

      addDecl (.thmDecl ruleWithDefInfo)
      FTrans.funTransRuleAttr.attr.add ruleWithDefName (← `(attr|ftrans)) .global



syntax extraAssumptions := "assume" bracketedBinder*

open Lean.Parser.Tactic.Conv 
-- syntax "#generate_revCDeriv" term num* " by " convSeq : command
syntax "#generate_fwdCDeriv" term ident* ("|" ident*)? (extraAssumptions)? " prop_by " tacticSeq " trans_by " convSeq : command

elab_rules : command
| `(#generate_fwdCDeriv $fnStx $mainArgs:ident* $[| $trailingArgs:ident* ]? $[$as:extraAssumptions]? prop_by $t:tacticSeq trans_by $rw:convSeq) => do
  Command.liftTermElabM do
    let mainArgs := mainArgs.map (fun a => a.getId)
    let trailingArgs : Array Name := 
      match trailingArgs with
      | .some trailingArgs => trailingArgs.map (fun a => a.getId)
      | none => #[]
    let fn ← elabTerm fnStx none
    let .some constName := fn.getAppFn'.constName?
      | throwError "unknown function {fnStx}"
    let extraBinders : Array Syntax := 
      match as with
      | .none => #[]
      | .some s =>
        match s with
        | `(extraAssumptions| assume $bs:bracketedBinder*) => bs
        | _ => #[]
    generateFwdCDeriv constName mainArgs trailingArgs t (← `(conv| ($rw))) extraBinders
