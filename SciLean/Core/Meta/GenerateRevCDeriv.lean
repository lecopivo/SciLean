import SciLean.Core.Meta.GenerateBasic
import SciLean.Lean.Name

namespace SciLean.Meta

open Lean Meta Qq

namespace GenerateProperty


structure GenerateData where
  /-- field over which we are currently working -/
  K : Expr
  
  /-- original context fvars of a function, these are types, instances and implicit arguments -/
  orgCtx : Array Expr 
  /-- extended orgCtx such that types form appropriate vector space, group or whatever is necessary -/
  ctx : Array Expr 

  /-- main fvars, main arguments we perform function transformation in -/
  mainArgs : Array Expr
  /-- unused fvars -/
  unusedArgs : Array Expr
  /-- trailing fvars -/
  trailingArgs : Array Expr
  /-- argument kinds, this allows to glue arguments back together with mergeArgs and mergeArgs' -/
  argKinds : Array ArgKind

  /-- names of main arguments guaranteed to be in the same order as mainArgs -/
  mainNames : Array Name

  /-- auxiliary type we perform transformation in -/
  W : Expr
  /-- fvar of type W -/
  w : Expr
  /-- fvars making W into vector space, group, or what ever is necessary -/
  ctxW : Array Expr

  /-- function we are working with as a function of `w` -/
  f : Expr
 
  /-- fvars that that are main arguments parametrized by W-/
  argFuns : Array Expr
  /-- fvars for properties about argFun -/
  argFunProps : Array Expr

  /-- declaration suffix based on argument names used to generate rule name -/
  declSuffix : String
  
  /-- level parameters -/
  levelParams : List Name


/-- Introduce new fvars such that the type `type` have instance of `SemiInnerProductSpace K ·` -/
partial def extendContextForType {α : Type _}
  {u} (K : Q(Type $u)) (type : Expr) (k : Array Expr → MetaM α) : MetaM α := do
  let cls ← mkAppM ``SemiInnerProductSpace #[K, type]
  match ← synthInstance? cls with
  | .some _ => k #[]
  | none => loop type #[]
where 
  loop (T : Expr) (acc : Array Expr) : MetaM α := do
    match T with
    | .forallE _ X Y _ =>
      if Y.hasLooseBVars then
        throwError "can't extend context for dependent type `{← ppExpr T}`"
      let .some ⟨v,X⟩ ← isTypeQ X
        | throwError "invalid type {← ppExpr X}"
      let cls := (Expr.const ``EnumType [v,u,u]).app X
      match ← synthInstance? cls with
      | .some _ => loop Y acc
      | none => 
        withLocalDecl `inst .instImplicit cls fun inst =>
          loop Y (acc.push inst)
    | .fvar _ => 
      let cls ← mkAppM ``SemiInnerProductSpace #[K, T]
      match ← synthInstance? cls with
      | .some _ => k acc
      | none => 
        withLocalDecl `inst .instImplicit cls fun inst => 
          k (acc.push inst)
    | _ => 
      throwError "dont' know how to extend context for the type `{← ppExpr T}`"

/-- Introduce new fvars such that every type in `types` have instance of `SemiInnerProductSpace K ·` -/
partial def extendContextImpl {α : Type _}
  {u} (K : Q(Type $u)) (types : Array Expr)
  (k : Array Expr → MetaM α) : MetaM α :=
  loop 0 #[]
where 
  loop (i : Nat) (acc : Array Expr) : MetaM α := do
    if h : i < types.size then
      let type := types[i]
      extendContextForType K type fun xs => loop (i+1) (acc ++ xs)
    else
      k acc

def extendContext {α : Type _} [MonadControlT MetaM n] [Monad n]
  {u} (K : Q(Type $u)) (types : Array Expr) (k : Array Expr → n α) : n α :=
  map1MetaM (fun k => extendContextImpl K types k) k

open Elab 
private def withGenerateData {α : Type _} [Inhabited α]
  (constName : Name) (mainNames trailingNames : Array Name) 
  (k : GenerateData → TermElabM α) : TermElabM α := do 
  let info ← getConstInfoDefn constName

  forallTelescope info.type fun xs type => do

    let (orgCtx, args) ← splitToCtxAndArgs xs

    let .some ⟨_u,K,_isROrC⟩ ← getFieldOutOfContextQ xs
      | throwError "unable to figure out what is the field"

    trace[Meta.generate_ftrans] "detected field {← ppExpr K}"

    let (mainArgs, unusedArgs, trailingArgs, argKinds) 
      ← splitArgs args mainNames trailingNames

    -- ensure that `mainNames` are in the right order
    let mainNames ← mainArgs.mapM (fun arg => arg.fvarId!.getUserName)
    let trailingNames ← trailingArgs.mapM (fun arg => arg.fvarId!.getUserName)

    let mut declSuffix := "arg_" ++ mainNames.joinl (fun n => toString n) (·++·)
    if trailingNames.size ≠ 0 then
      declSuffix := declSuffix ++ "_" ++ trailingNames.joinl (fun n => toString n) (·++·)

    let types := (← liftM <| mainArgs.mapM inferType).push (← mkForallFVars trailingArgs type)
    extendContext K types fun ctx' => do

    trace[Meta.generate_ftrans] "extending context with {← liftM <| ctx'.mapM fun c => do pure s!"({← ppExpr c} : {← ppExpr (← inferType c)})"}"
    
    let ctx := orgCtx ++ ctx'

    checkNoDependentTypes mainArgs xs

    let vLvlName := mkUnusedName info.levelParams `w
    -- let v ← mkFreshLevelMVar
    let v := Level.param vLvlName
    withLocalDeclQ `W .implicit q(Type $v) fun W => do
    withLocalDecl `instW .instImplicit (← mkAppM ``SemiInnerProductSpace #[K,W]) fun instW => do
    withLocalDeclQ (u:=v) `w .default W fun w => do

    -- argFuns are selected arguments parametrized by `W`
    let argFunDecls :=
      mkLocalDecls mainNames .default (← mainArgs.mapM fun arg => do mkArrow W (← inferType arg))

    withLocalDecls argFunDecls fun argFuns => do

      let argFunApps := argFuns.map (fun argFun => argFun.app w)

      let f ← 
        withLetDecls mainNames argFunApps fun args' => do
          let xs' := orgCtx ++ mergeArgs args' unusedArgs trailingArgs argKinds
          mkLambdaFVars ((#[w] : Array Expr) ++ trailingArgs ++ args') (← mkAppOptM constName (xs'.map Option.some))

      let argFunPropDecls := 
        mkLocalDecls (n:=TermElabM)
          (mainNames.map (fun name => name.appendBefore "h"))
          .default 
          (← liftM <| argFuns.mapM fun argFun => mkAppM ``HasAdjDiff #[K,argFun])

      withLocalDecls argFunPropDecls fun argFunProps => do
        let data : GenerateData := {
          K := K
          orgCtx := orgCtx
          ctx := ctx

          mainArgs := mainArgs
          unusedArgs := unusedArgs
          trailingArgs := trailingArgs
          argKinds := argKinds

          mainNames := mainNames
          
          W := W
          w := w
          ctxW := #[instW]

          f := f
        
          argFuns := argFuns
          argFunProps := argFunProps

          levelParams := vLvlName :: info.levelParams

          declSuffix := declSuffix
        }
        k data


/-- 
Replaces `<∂ fᵢ x` with `Tfᵢ` in `e`
- `argFuns = #[f₁, ..., fₙ]`
- `transArgFuns = #[<∂ f₁ x, ..., <∂ fₙ x]`
- `transArgFunVars  = #[Tf₁, ..., Tfₙ]`

Throws an error if all `fᵢ` has not been liminated from `e`
-/
def eliminateTransArgFun (e : Expr) (argFuns transArgFuns transArgFunVars : Array Expr) : MetaM Expr := do
  let e' ←
    e.replaceM (fun x => do
      if x.hasLooseBVars then
        pure .noMatch
      else
        if let .some i ← transArgFuns.findIdxM? (isDefEq · x) then
          pure (.yield transArgFunVars[i]!)
        else 
          pure .noMatch)

  if let .some i := argFuns.findIdx? (fun argFun => e'.containsFVar argFun.fvarId!) then
    throwError "failed to perform function transformation, can't elimate {← ppExpr argFuns[i]!} out of transformed function{←ppExpr e}\n it is expected that {← ppExpr argFuns[i]!} appears only in {← ppExpr transArgFuns[i]!}"

  return e'

end GenerateProperty

open Lean Elab Term

open GenerateProperty

def generateRevCDeriv (constName : Name) (mainNames trailingNames : Array Name) (conv : TSyntax `conv) : TermElabM Unit := do
  
  withGenerateData constName mainNames trailingNames fun data => do
    
    let lhs ← mkAppM ``revCDeriv #[data.K, data.f]
    trace[Meta.generate_ftrans] "lhs for revCDeriv rule\n{← ppExpr lhs}"

    let (rhs, proof) ← elabConvRewrite lhs conv
    trace[Meta.generate_ftrans] "rhs for revCDeriv rule\n{← ppExpr rhs}"

    if (rhs == lhs) then 
      throwError "failed to perform function transformation, zero progress"

    let .lam _ _ b _ := rhs
      | throwError "transformed function should be in the form `fun w => ...` but got\n{← ppExpr rhs}"

    let b := b.instantiate1 data.w

    let transArgFuns ← 
      data.argFuns.mapM (fun argFun => mkAppM ``revCDeriv #[data.K, argFun, data.w])

    let dArgDecls := 
      mkLocalDecls (n := TermElabM)
        (data.mainNames.map (fun n => n.appendBefore "d" |>.appendAfter "'"))
        .default 
        (← liftM <| data.mainArgs.mapM (fun arg => do mkArrow (← inferType arg) data.W))

    withLocalDecls dArgDecls fun dArgs => do

    let transArgVars ← (data.mainArgs.zip dArgs).mapM (fun (x,dx') => mkAppM ``Prod.mk #[x,dx'])
    -- find all occurances of `<∂ (w':=w), argFunᵢ w` and replace it with recently introduced fvar
    let b' ← eliminateTransArgFun b data.argFuns transArgFuns transArgVars
    if b'.containsFVar data.w.fvarId! then
      throwError s!"failed to perform function transformation, transformed function still contains auxiliary variable {← ppExpr data.w}\n{← ppExpr b'}"


    let transFunArgs := (data.ctx ++ #[data.W] ++ data.ctxW ++ mergeArgs' data.mainArgs data.unusedArgs data.argKinds ++ dArgs)
    let transFun ← instantiateMVars (← mkLambdaFVars transFunArgs b')
    let transFun ← LetNormalize.letNormalize transFun {}
    let transFunName := constName.append data.declSuffix |>.append "revCDeriv"
    trace[Meta.generate_ftrans] "generated revCDeriv function {transFunName}\n{← ppExpr transFun}"

    let transFunInfo : DefinitionVal := 
    {
      name  := transFunName
      type  := (← inferType transFun)
      value := transFun
      hints := .regular 0
      safety := .safe
      levelParams := data.levelParams
    }

    addAndCompile (.defnDecl transFunInfo)

    let ruleArgs := data.ctx ++ #[data.W] ++ data.ctxW ++ mergeArgs' data.argFuns data.unusedArgs data.argKinds ++ data.argFunProps
    let ruleProof ← instantiateMVars (← mkLambdaFVars ruleArgs proof)
    let ruleName := constName.append data.declSuffix |>.append "revCDeriv_rule"
    trace[Meta.generate_ftrans] "revCDeriv rule {ruleName}\n{← ppExpr (← inferType ruleProof)}"

    if (← inferType ruleProof).hasMVar then
      throwError "rule has meta variables\n{← ppExpr (← inferType ruleProof)}"

    if ruleProof.hasMVar then
      throwError "rule proof has meta variables\n{← ppExpr ruleProof}"

    let ruleInfo : TheoremVal := 
    {
      name  := ruleName
      type  := ← instantiateMVars (← inferType ruleProof)
      value := ruleProof
      levelParams := data.levelParams
    }

    addDecl (.thmDecl ruleInfo)

    withLetDecls data.mainNames transArgFuns fun transArgFunLets => do

      let argVals ← transArgFunLets.mapM (fun x => mkAppM ``Prod.fst #[x])
      let dArgVals ← transArgFunLets.mapM (fun x => mkAppM ``Prod.snd #[x])

      let lvls := data.levelParams.map Level.param
      let transFunArgs := data.ctx ++ #[data.W] ++ data.ctxW ++ mergeArgs' argVals data.unusedArgs data.argKinds ++ dArgVals
      let rhs ← 
        mkLambdaFVars 
          ((#[data.w] : Array Expr) ++ transArgFunLets) 
          (mkAppN (.const transFunName lvls) transFunArgs)


      let ruleDefArgs := data.ctx ++ #[data.W] ++ data.ctxW ++ mergeArgs' data.argFuns data.unusedArgs data.argKinds ++ data.argFunProps
      let ruleDef ← instantiateMVars (← mkForallFVars ruleDefArgs (← mkEq lhs rhs))
      let ruleDefName := constName.append data.declSuffix |>.append "revCDeriv_rule_def"

      trace[Meta.generate_ftrans] "revCDeriv def rule {ruleDefName}\n{← ppExpr ruleDef}"

      let ruleDefInfo : TheoremVal := 
      {
        name  := ruleDefName
        type  := ruleDef
        value := ruleProof
        levelParams := data.levelParams
      }

      addDecl (.thmDecl ruleDefInfo)

open Lean.Parser.Tactic in
def generateHasAdjDiff (constName : Name) (mainNames trailingNames : Array Name) (tac : TSyntax ``tacticSeq) : TermElabM Unit := do
  
  withGenerateData constName mainNames trailingNames fun data => do
    
    let statement ← mkAppM ``HasAdjDiff #[data.K, data.f]
    trace[Meta.generate_ftrans] "statement for HasAdjDiff\n{← ppExpr statement}"

    let proof ← Meta.mkFreshExprMVar statement

    let goals ← Tactic.run proof.mvarId! do
      Tactic.evalTactic tac

    if ¬goals.isEmpty then
      throwError s!"unsolved goals {← liftM <| goals.mapM (fun m => m.getType >>= ppExpr)}"

    let args := data.ctx ++ #[data.W] ++ data.ctxW ++ mergeArgs' data.argFuns data.unusedArgs data.argKinds ++ data.argFunProps
    let proof ← instantiateMVars (← mkLambdaFVars args proof)
    let type ← inferType proof
    let name := constName.append data.declSuffix |>.append "HasAdjDiff_rule"
    trace[Meta.generate_ftrans] "HasAdjDiff rule for `{constName}`\n{← ppExpr type}"

    let info : TheoremVal := 
    {
      name  := name
      type  := type
      value := proof
      levelParams := data.levelParams
    }

    addDecl (.thmDecl info)




open Lean.Parser.Tactic.Conv 
-- syntax "#generate_revCDeriv" term num* " by " convSeq : command
syntax "#generate_revCDeriv" term ident* ("|" ident*)? " by " convSeq : command
syntax "#generate_HasAdjDiff" term ident* ("|" ident*)? " by " tacticSeq : command


elab_rules : command
| `(#generate_revCDeriv $fnStx $mainArgs:ident* $[| $trailingArgs:ident* ]? by $rw:convSeq) => do
  Command.liftTermElabM do
    let mainArgs := mainArgs.map (fun a => a.getId)
    let trailingArgs : Array Name := 
      match trailingArgs with
      | .some trailingArgs => trailingArgs.map (fun a => a.getId)
      | none => #[]
    let fn ← elabTerm fnStx none
    let .some constName := fn.getAppFn'.constName?
      | throwError "unknown function {fnStx}"
    generateRevCDeriv constName mainArgs trailingArgs (← `(conv| ($rw)))


elab_rules : command
| `(#generate_HasAdjDiff $fnStx $mainArgs:ident* $[| $trailingArgs:ident* ]? by $prf:tacticSeq) => do
  Command.liftTermElabM do
    let mainArgs := mainArgs.map (fun a => a.getId)
    let trailingArgs : Array Name := 
      match trailingArgs with
      | .some trailingArgs => trailingArgs.map (fun a => a.getId)
      | none => #[]
    let fn ← elabTerm fnStx none
    let .some constName := fn.getAppFn'.constName?
      | throwError "unknown function {fnStx}"
    generateHasAdjDiff constName mainArgs trailingArgs prf
