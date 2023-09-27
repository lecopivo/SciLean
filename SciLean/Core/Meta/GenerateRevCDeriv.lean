import SciLean.Core.Meta.GenerateBasic
import SciLean.Core.Meta.ExtendContext
import SciLean.Core.Meta.ParametrizeFVars
import SciLean.Tactic.LetNormalize
import SciLean.Tactic.AnalyzeConstLambda
import SciLean.Lean.Name

namespace SciLean.Meta

open Lean Meta Elab Term Qq Lean.Parser.Tactic

namespace GenerateRevCDeriv

open GenerateProperty

def generateRevCDeriv (constName : Name) (mainNames trailingNames : Array Name) 
  (tac : TSyntax ``tacticSeq) (conv : TSyntax `conv) : TermElabM Unit := do
  let info ← getConstInfoDefn constName

  forallTelescope info.type fun xs returnType => do

    let (ctx, args) ← splitToCtxAndArgs xs
    
    let .some ⟨_u,K,_isROrC⟩ ← getFieldOutOfContextQ ctx
      | throwError "unable to figure out what is the field"

    trace[Meta.generate_ftrans] "detected field {← ppExpr K}"

    let (mainArgs, unusedArgs, trailingArgs, argKinds) 
      ← splitArgs args mainNames trailingNames

    let returnType ← mkForallFVars trailingArgs returnType

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
    withSemiInnerProductSpaces K (mainTypes.push returnType) fun vecInsts => do

    let vLvlName := mkUnusedName info.levelParams `w
    let v := Level.param vLvlName
    let lvlParams := vLvlName :: info.levelParams
    withLocalDecl `W .implicit (mkSort v.succ) fun W => do
    withSemiInnerProductSpace K W fun instW => do
    withLocalDecl `w .default W fun w => do

    withParametrizedFVars w mainArgs #[lhsExpr, rhsExpr] fun _ lhsrhs => do

    let decls :=
      mkLocalDecls (n:=TermElabM)
        (mainNames.map (fun n => n.appendBefore "h")) 
        .default
        (← mainArgs.mapM (fun arg => do 
          lambdaTelescope (← etaExpand arg) fun xs b => do
            let f := (← mkLambdaFVars #[xs[0]!] b).eta
            let prop ← mkAppM ``HasAdjDiff #[K,f]
            mkForallFVars xs[1:] prop))


    withLocalDecls decls fun mainArgProps => do

      let f ← mkLambdaFVars (#[w]++trailingArgs) lhsrhs[0]!

      let lhs ← mkAppM ``revCDeriv #[K, f]

      let rhs ← mkLambdaFVars (#[w]++trailingArgs) lhsrhs[1]!
      let rhs ← mkAppM ``revCDeriv #[K, rhs]

      let isDiff ← mkAppM ``HasAdjDiff #[K, f]

      let (rhs, proof) ← elabConvRewrite rhs conv
      let isDiffProof ← elabProof isDiff tac
    
      let .lam _ _ rhsBody _ := rhs
        | throwError "unexpected result after function transformation, expecting `fun w => ...` but got\n{←ppExpr rhs}"

      let rhsBody := rhsBody.instantiate #[w]
      let dargs ← mainArgs.mapM (fun arg => mkAppM ``revCDeriv #[K,arg,w])

      let revDerivFun ← do
        withLocalDecls' mainNames .default mainTypes fun ys => do
        let names := mainNames.map (fun n => n.appendBefore "d" |>.appendAfter "'")
        let types ← mainTypes.mapM (fun t => mkArrow t W)
        withLocalDecls' names .default types fun dys => do
          let dargs' ← ys.mapIdxM (fun i y => mkAppM ``Prod.mk #[y,dys[i]!])
          let rhsBody' ← rhsBody.replaceExprs dargs dargs' 
          let rhsBody' ← LetNormalize.letNormalize rhsBody' {}

          if rhsBody'.containsFVar w.fvarId! then
            throwError "failed to eliminate auxiliary variable `{← ppExpr w}` from\n{← ppExpr rhsBody'}"

          let args := ctx ++ #[W] ++ instW ++ vecInsts ++ mergeArgs' ys unusedArgs argKinds ++ dys
          let revDerivFun ← mkLambdaFVars args rhsBody'
          pure revDerivFun
      let revDerivFun ← instantiateMVars revDerivFun

      -- calling `analyzeConstLambda` here is bit of an overkill as we are only
      -- interested in `declSuffix`
      let lhsData ← analyzeConstLambda f

      let revDerivFunName := 
        constName.append lhsData.declSuffix |>.append "revCDeriv"
      let ruleName := revDerivFunName.appendAfter "_rule"
      let ruleWithDefName := revDerivFunName.appendAfter "_rule_def"
      let isDiffRuleName := 
        constName.append lhsData.declSuffix |>.append "HasAdjDiff_rule"

      let xs' := ctx ++ #[W] ++ instW ++ vecInsts ++ args ++ mainArgProps
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

      let rule ← mkForallFVars xs' (← mkEq lhs rhs) >>= instantiateMVars
      let proof ← mkLambdaFVars xs' proof >>= instantiateMVars

      let ruleInfo : TheoremVal := 
      {
        name  := ruleName
        type  := rule
        value := proof
        levelParams := lvlParams
      }

      addDecl (.thmDecl ruleInfo)

      let revDerivFunInfo : DefinitionVal := 
      {
        name  := revDerivFunName
        type  := (← inferType revDerivFun)
        value := revDerivFun
        hints := .regular 0
        safety := .safe
        levelParams := lvlParams
      }

      addAndCompile (.defnDecl revDerivFunInfo)

      let rhsWithDef ← do
        let names := mainNames.map (fun n => Name.mkSimple s!"{n}d{n}'")
        withLetDecls names dargs fun ydys => do
          let ys ← ydys.mapM (fun ydy => mkAppM ``Prod.fst #[ydy])
          let dys ← ydys.mapM (fun ydy => mkAppM ``Prod.snd #[ydy])
          let args := ctx ++ #[W] ++ instW ++ vecInsts ++ mergeArgs' ys unusedArgs argKinds ++ dys
          let lvls := lvlParams.map (fun p => Level.param p)
          let body := (mkAppN (.const revDerivFunName lvls) args)
          mkLambdaFVars (#[w] ++ ydys) body

      let ruleWithDef ← mkForallFVars xs' (← mkEq lhs rhsWithDef) >>= instantiateMVars

      let ruleWithDefInfo : TheoremVal := 
      {
        name  := ruleWithDefName
        type  := ruleWithDef
        value := proof
        levelParams := lvlParams
      }

      addDecl (.thmDecl ruleWithDefInfo)


open Lean.Parser.Tactic.Conv 

syntax "#generate_revCDeriv" term ident* ("|" ident*)? " prop_by " tacticSeq " trans_by " convSeq : command

elab_rules : command
| `(#generate_revCDeriv $fnStx $mainArgs:ident* $[| $trailingArgs:ident* ]? prop_by $t:tacticSeq trans_by $rw:convSeq) => do
  Command.liftTermElabM do
    let mainArgs := mainArgs.map (fun a => a.getId)
    let trailingArgs : Array Name := 
      match trailingArgs with
      | .some trailingArgs => trailingArgs.map (fun a => a.getId)
      | none => #[]
    let fn ← elabTerm fnStx none
    let .some constName := fn.getAppFn'.constName?
      | throwError "unknown function {fnStx}"
    generateRevCDeriv constName mainArgs trailingArgs t (← `(conv| ($rw)))

