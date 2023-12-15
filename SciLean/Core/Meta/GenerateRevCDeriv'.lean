import SciLean.Core.Meta.GenerateBasic
import SciLean.Core.Meta.ExtendContext
import SciLean.Core.Meta.ParametrizeFVars
import SciLean.Tactic.LetNormalize
import SciLean.Tactic.AnalyzeConstLambda
import SciLean.Tactic.LSimp2.Elab
import SciLean.Lean.Name
import SciLean.Core.Notation

namespace SciLean.Meta

open Lean Meta Elab Term Qq Lean.Parser.Tactic

namespace GenerateRevCDeriv'

open GenerateProperty

inductive FTransRuleType where | withDef | noDef


def generateRevCDeriv (constName : Name) (mainNames trailingNames : Array Name) (ruleType : FTransRuleType)
  (tac : TSyntax ``tacticSeq) (conv : TSyntax `conv) : TermElabM Unit := do
  let info ← getConstInfoDefn constName

  forallTelescope info.type fun xs returnType => do

    let (ctx, args) ← splitToCtxAndArgs xs
    
    let .some ⟨_u,K,_isROrC⟩ ← getFieldOutOfContextQ xs
      | throwError "unable to figure out what is the field"

    trace[Meta.generate_ftrans] "detected field {← ppExpr K}"

    let (mainArgs, unusedArgs, trailingArgs, argKinds)
      ← splitArgs args mainNames trailingNames

    let returnType ← mkForallFVars trailingArgs returnType

    -- ensure that `mainNames` and `trailingNames` are in the right order
    let mainNames ← mainArgs.mapM (fun arg => arg.fvarId!.getUserName)
    let trailingNames ← trailingArgs.mapM (fun arg => arg.fvarId!.getUserName)
    -- sufix used in declaration names indicating which arguments are main and trailing
    let argSuffix' := 
      "arg_" ++ mainNames.foldl (init:="") (·++toString ·)
    let argSuffix := 
      if trailingArgs.size = 0 then 
        argSuffix'
      else 
        argSuffix' ++ trailingNames.foldl (init:="_") (·++toString ·)
  
    let lvls := info.levelParams.map fun p => Level.param p
    let f ← liftM <|
      mkLambdaFVars (mainArgs++trailingArgs) (mkAppN (Expr.const constName lvls) xs)
      >>=
      mkUncurryFun mainArgs.size


    let mainTypes ← liftM <| mainArgs.mapM inferType
    withSemiInnerProductSpaces K (mainTypes.push returnType) fun extraInsts => do

    -- Simple Rules ------------------------------------------------------------

    -- HasAdjDiff rule --
    ---------------------

    let f' ← liftM <|
      mkLambdaFVars (mainArgs) (mkAppN (Expr.const constName lvls) xs)
      >>=
      mkUncurryFun mainArgs.size

    let funProp ← mkAppM ``HasAdjDiff #[K, f']
    let propProof ← elabProof funProp tac

    let hasAdjDiffName := constName.append argSuffix' |>.append "HasAdjDiff_rule_simple"
    let hasAdjDiffProof ← mkLambdaFVars (ctx++extraInsts++unusedArgs++trailingArgs) propProof >>= instantiateMVars
    let hasAdjDiffInfo : TheoremVal := 
    {
      name  := hasAdjDiffName
      type  := (← inferType hasAdjDiffProof)
      value := hasAdjDiffProof
      levelParams := info.levelParams
    }

    addDecl (.thmDecl hasAdjDiffInfo)
    FProp.funTransRuleAttr.attr.add hasAdjDiffName (← `(attr|fprop)) .global

    -- revCDeriv definition --
    --------------------------

    let lhs ← mkAppM ``revCDeriv #[K, f]
    let (rhs,proof) ← elabConvRewrite lhs conv

    let xs := ctx++extraInsts++mergeArgs' mainArgs unusedArgs argKinds
    let revDerivFun ← liftM <|
      mkLambdaFVars xs (rhs.beta #[(← mkProdElem mainArgs)])
    let revDerivFunName := constName.append argSuffix |>.append "revCDeriv"
    let (revDerivFun,_) ← elabConvRewrite revDerivFun (← `(conv| lsimp (config := {zeta:=false}) only))
    let revDerivFunInfo : DefinitionVal := 
    {
      name  := revDerivFunName
      type  := (← inferType revDerivFun)
      value := revDerivFun
      hints := .regular 0
      safety := .safe
      levelParams := info.levelParams
    }

    addAndCompile (.defnDecl revDerivFunInfo)


    -- revCDeriv rule without definition --
    ---------------------------------------

    let xs := (ctx++extraInsts++unusedArgs)
    let rule_simple ← mkForallFVars xs (← mkEq lhs rhs) >>= instantiateMVars
    let rule_simple_proof ← mkLambdaFVars xs proof >>= instantiateMVars

    let ruleSimpleName := constName.append argSuffix |>.append "revCDeriv_rule_simple"
    let ruleSimpleInfo : TheoremVal := 
    {
      name  := ruleSimpleName
      type  := rule_simple
      value := rule_simple_proof
      levelParams := info.levelParams
    }

    addDecl (.thmDecl ruleSimpleInfo)

    -- revCDeriv rule with definition --
    ------------------------------------

    let xs := (ctx++extraInsts++unusedArgs)
    let p ← mkProdElem mainArgs
    let rhs' ←
      withLocalDeclD `x (← inferType p) fun pVar => do
        let ps ← mkProdSplitElem pVar mainArgs.size
        let xs := (ctx++extraInsts++mergeArgs' ps unusedArgs argKinds)
        mkLambdaFVars #[pVar] (mkAppN (.const revDerivFunName lvls) xs)
    let rule_simple_def ← mkForallFVars xs (← mkEq lhs rhs') >>= instantiateMVars
    let rule_simple_def_proof ← mkLambdaFVars xs proof >>= instantiateMVars

    let ruleSimpleDefName := constName.append argSuffix |>.append "revCDeriv_rule_def_simple"
    let ruleSimpleDefInfo : TheoremVal := 
    {
      name  := ruleSimpleDefName
      type  := rule_simple_def
      value := rule_simple_def_proof
      levelParams := info.levelParams
    }

    addDecl (.thmDecl ruleSimpleDefInfo)

    match ruleType with
    | .withDef =>
      FTrans.funTransRuleAttr.attr.add ruleSimpleDefName (← `(attr|ftrans)) .global
    | .noDef => 
      FTrans.funTransRuleAttr.attr.add ruleSimpleName (← `(attr|ftrans)) .global


    -- Composition Rules -------------------------------------------------------

    let vLvlName := mkUnusedName info.levelParams `w
    let v := Level.param vLvlName
    let lvlParams := vLvlName :: info.levelParams
    withLocalDecl `W .implicit (mkSort v.succ) fun W => do
    withSemiInnerProductSpace K W fun instW => do
    withLocalDecl `w .default W fun w => do

    withParametrizedFVars w mainArgs #[] fun _ _ => do
    withLocalDecls' (mainNames.map (fun n => n.appendBefore "h"))
                    .default
                    (← mainArgs.mapM fun x => mkAppM ``HasAdjDiff #[K,x]) fun mainArgProps => do
      
      let f₁ := f'
      let f₂ ← mkLambdaFVars #[w] (← mkProdElem (mainArgs.map (fun arg => arg.app w)))

      let xs := ctx ++ mergeArgs (mainArgs.map (fun arg => arg.app w)) unusedArgs trailingArgs argKinds
      let fn ← mkLambdaFVars #[w] (mkAppN (.const constName lvls) xs)
      let prop ← mkAppM ``HasAdjDiff #[K,fn]


      -- HasAdjDiff comp rule --
      --------------------------

      let (.some propProof, _) ← HasAdjDiff.fpropExt.compRule prop f₁ f₂ |>.run {} |>.run {}
        | throwError "failed to create composition rule for HasAdjDiff"

      let xs := ctx ++ extraInsts ++ #[W] ++ instW ++ mergeArgs mainArgs unusedArgs trailingArgs argKinds ++ mainArgProps
      let hasAdjDiffName := constName.append argSuffix' |>.append "HasAdjDiff_rule"
      let hasAdjDiffRule ← mkForallFVars xs prop >>= instantiateMVars
      let hasAdjDiffProof ← mkLambdaFVars xs propProof >>= instantiateMVars
      let hasAdjDiffInfo : TheoremVal := 
      {
        name  := hasAdjDiffName
        type  := hasAdjDiffRule
        value := hasAdjDiffProof
        levelParams := lvlParams
      }

      addDecl (.thmDecl hasAdjDiffInfo)
      FProp.funTransRuleAttr.attr.add hasAdjDiffName (← `(attr|fprop)) .global


      -- revCDeriv comp rule --
      -------------------------

      let f₁ := f
      let f₂ ← mkLambdaFVars #[w] (← mkProdElem (mainArgs.map (fun arg => arg.app w)))

      let xs := ctx ++ mergeArgs (mainArgs.map (fun arg => arg.app w)) unusedArgs trailingArgs argKinds
      let fn ← mkLambdaFVars (#[w]++trailingArgs) (mkAppN (.const constName lvls) xs)
      let lhs ← mkAppM ``revCDeriv #[K,fn]

      let (.some step, _) ← revCDeriv.ftransExt.compRule lhs f₁ f₂ |>.run {} |>.run {}
        | throwError "failed to create composition rule revCDeriv"

      let rhs' := step.result.expr
      let h' ← step.result.getProof
      let (rhs'', h'') ← elabConvRewrite rhs' (← `(conv| ftrans only))
      
      let xs := ctx ++ extraInsts ++ #[W] ++ instW ++ mergeArgs' mainArgs unusedArgs argKinds ++ mainArgProps
      let rule ← mkForallFVars xs (← mkEq lhs rhs'') >>= instantiateMVars
      let ruleProof ← mkLambdaFVars xs (← mkEqTrans h' h'') >>= instantiateMVars


      let ruleName := constName.append argSuffix |>.append "revCDeriv_rule"
      let ruleInfo : TheoremVal := 
      {
        name  := ruleName
        type  := rule
        value := ruleProof
        levelParams := lvlParams
      }

      addDecl (.thmDecl ruleInfo)
      FTrans.funTransRuleAttr.attr.add ruleName (← `(attr|ftrans)) .global


open Lean.Parser.Tactic.Conv 

syntax "#generate_revCDeriv'" term ident* ("|" ident*)? " prop_by " tacticSeq " trans_by " convSeq : command

elab_rules : command
| `(#generate_revCDeriv' $fnStx $mainArgs:ident* $[| $trailingArgs:ident* ]? prop_by $t:tacticSeq trans_by $rw:convSeq) => do
  Command.liftTermElabM do
    let mainArgs := mainArgs.map (fun a => a.getId)
    let trailingArgs : Array Name := 
      match trailingArgs with
      | .some trailingArgs => trailingArgs.map (fun a => a.getId)
      | none => #[]
    let fn ← elabTerm fnStx none
    let .some constName := fn.getAppFn'.constName?
      | throwError "unknown function {fnStx}"
    generateRevCDeriv constName mainArgs trailingArgs .withDef t (← `(conv| ($rw)))

#exit

variable 
  {K : Type} [RealScalar K]
  {X : Type} [SemiInnerProductSpace K X]
  {X₁ : Type} [SemiInnerProductSpace K X₁]
  {X₂ : Type} [SemiInnerProductSpace K X₂]
  {Y : Type} [SemiInnerProductSpace K Y]
  {Z : Type} [SemiInnerProductSpace K Z]
  {W : Type} [SemiInnerProductSpace K W]
  {ι : Type} [EnumType ι]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)]

set_default_scalar K

def mul (x y : K) : K := x * y

#generate_revCDeriv' mul x y
  prop_by unfold mul; fprop
  trans_by unfold mul; ftrans; ftrans

#print mul.arg_xy.revCDeriv
#check mul.arg_xy.revCDeriv_rule_simple
#check mul.arg_xy.revCDeriv_rule
#check mul.arg_xy.revCDeriv_rule_def_simple
#check mul.arg_xy.HasAdjDiff_rule_simple
#check mul.arg_xy.HasAdjDiff_rule

def add (x y : X) : X := x + y

#generate_revCDeriv' add x y
  prop_by unfold add; fprop
  trans_by unfold add; ftrans; ftrans

#print add.arg_xy.revCDeriv
#check add.arg_xy.revCDeriv_rule_simple
#check add.arg_xy.revCDeriv_rule_def_simple
#check add.arg_xy.HasAdjDiff_rule_simple

def smul {X : Type} [SemiHilbert K X]
 (x : K) (y : X) : X := x • y

set_option trace.Meta.Tactic.fprop.discharge true in
#generate_revCDeriv' smul x y
  prop_by unfold smul; fprop
  trans_by unfold smul; ftrans; ftrans


set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.simp.unify true in
#check 
  (<∂ (xy : K×K), mul xy.1 xy.2)
  rewrite_by
    ftrans only

set_option trace.Meta.Tactic.simp.rewrite true in
set_option trace.Meta.Tactic.simp.unify true in
#check 
  (<∂ (x : K), mul x x)
  rewrite_by
    ftrans only


#check FunLike


set_option trace.Meta.Tactic.simp.rewrite true in
set_option trace.Meta.Tactic.simp.unify true in
#check 
  (<∂ (x : K), 
    let x1 := mul x x
    let x2 := mul x1 (mul x x)
    let x3 := mul x2 (mul x1 x)
    let x4 := mul x3 (mul x2 x)
    let x5 := mul x4 (mul x3 x)
    x5)
  rewrite_by
    ftrans only


#check
  (<∂ (x : K), 
    let x1 := mul x x
    let x2 := mul x1 x1
    let x3 := mul x2 x2
    let x4 := mul x3 x3
    let x5 := mul x4 x4
    x5)
  rewrite_by
    ftrans


#check 
  (<∂ (x : K), 
    let x1 := mul x x
    let x2 := mul x1 x
    let x3 := mul x2 x
    let x4 := mul x3 x
    let x5 := mul x4 x
    x5)
  rewrite_by
    ftrans




