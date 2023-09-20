import SciLean.Core.Objects.FinVec
import SciLean.Core.FunctionTransformations
import SciLean.Core.Notation
import SciLean.Core.Meta.GenerateInit

namespace SciLean.Meta

open Lean Meta Qq


def isTypeQ (e : Expr) : MetaM (Option ((u : Level) × Q(Type $u))) := do
  let u ← mkFreshLevelMVar
  let .some e ← checkTypeQ e q(Type $u)
    | return none
  return .some ⟨u, e⟩

/-- Returns `(id, u, K)` where `K` is infered field type with universe level `u`

The index `id` tells that arguments `args[id:]` have already `K` in its local context with valid `IsROrC K` instances. -/
def getFieldOutOfContextQ (args : Array Expr) : MetaM (Option ((u : Level) × (K : Q(Type $u)) × Q(IsROrC $K))) := do

  let mut K? : Option Expr := none
  for arg in args do
    let type ← inferType arg

    if type.isAppOf ``IsROrC then
      K? := type.getArg! 0
      break

    if type.isAppOf ``Scalar then
      K? := type.getArg! 0
      break

    if type.isAppOf ``RealScalar then
      K? := type.getArg! 0
      break

    if type.isAppOf ``Vec then
      K? := type.getArg! 0
      break

    if type.isAppOf ``SemiInnerProductSpace then
      K? := type.getArg! 0
      break

    if type.isAppOf ``SemiHilbert then
      K? := type.getArg! 0
      break

    if type.isAppOf ``FinVec then
      K? := type.getArg! 1
      break

  let .some K := K? | return none
  let .some ⟨u,K⟩ ← isTypeQ K | return none
  let isROrC ← synthInstanceQ q(IsROrC $K)

  return .some ⟨u,K,isROrC⟩

def firstExplicitNonTypeIdx (xs : Array Expr) : MetaM Nat := do
  let mut i := 0
  for x in xs do
    let X ← inferType x
    if (← x.fvarId!.getBinderInfo) == .default && 
       ¬X.bindingBodyRec.isType then
      return i
    i := i + 1
  return i



/-- Checks that type `X` has instance of `SemiInnerProductSpace K ·`. Throws error if instance does not exists. 

TODO: return suggested class to make this succeed. 
For example:
- for `X = α` suggest class `SemiInnerProductSpace K α`
- for `X = ι → α` suggest classes `EnumType ι` and `SemiInnerProductSpace K α`.
- for `X = DataArrayN α ι` suggest classes `Index ι` and `SemiInnerProductSpace K α`.
-/
def  checkObjInstances (K : Expr) (X : Expr) : MetaM Unit := do
  -- check that return type form SemiInnerProductSpace
  let .some _semiInnerProductSpace ← synthInstance? (← mkAppM ``SemiInnerProductSpace #[K, X])
    | throwError "unable to synthesize `SemiInnerProductSpace` for the type {← ppExpr X}"

/-- Checks that types of `xᵢ` and `b` has instances of `SemiInnerProductSpace K ·`. Throws error if instance does not exists.
 -/
def  checkArgInstances (K : Expr) (xs : Array Expr) : MetaM Unit := do
  -- check that all arguments form SemiInnerProductSpace
  for x in xs do
    let X ← inferType x
    checkObjInstances K X
     

/-- Check that types of `ys` do not depend on fvars `xs` -/
def checkNoDependentTypes (xs ys : Array Expr) : MetaM Unit := do
  for y in ys do
    let Y ← inferType y
    if let .some x := xs.find? (fun x => Y.containsFVar x.fvarId!) then
      throwError s!"the type of ({← ppExpr y} : {← ppExpr (← inferType y)}) depends on the argument {← ppExpr x}, dependent types like this are not supported"
 

/-- Make local declarations is we have an array of names and types. -/
def mkLocalDecls [MonadControlT MetaM n] [Monad n] 
  (names : Array Name) (bi : BinderInfo) (types : Array Expr) : Array (Name × BinderInfo × (Array Expr → n Expr)) :=
  types.mapIdx (fun i type => (names[i]!, bi, fun _ : Array Expr => pure type))

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
    throwError "Failed to elimate {← ppExpr argFuns[i]!} out of transformed function{←ppExpr e}\n it is expected that {← ppExpr argFuns[i]!} appears only in {← ppExpr transArgFuns[i]!}"

  return e'

open Lean Elab Term

def generateRevCDeriv (constName : Name) (argIds : ArraySet Nat) (conv : TSyntax `conv) : TermElabM Unit := do
  let info ← getConstInfoDefn constName

  forallTelescope info.type fun xs type => do

    let (args, otherArgs, splitIds) := xs.splitIdx (fun i _ => i.1 ∈ argIds)

    let xsNames ← getConstArgNames constName true
    let argNames := argIds.toArray.map (fun i => xsNames[i]!)
    let argName := "arg_" ++ argNames.foldl (init := "") (·++ toString ·)

    trace[Meta.generate_ftrans] "generating revCDeriv for {constName} in arguments {← args.mapM fun arg => do pure s!"({←ppExpr arg} : {← ppExpr (← inferType arg)})"}"

    let .some ⟨u,K,_isROrC⟩ ← getFieldOutOfContextQ xs
      | throwError "unable to figure out what is the field"

    trace[Meta.generate_ftrans] "detected field {← ppExpr K}"

    -- few checks that we can do what we want to do
    checkObjInstances K type
    checkArgInstances K args
    checkNoDependentTypes args xs

    let vLvlName := `v
    -- let v ← mkFreshLevelMVar
    let v := Level.param vLvlName
    withLocalDeclQ `W .implicit q(Type $v) fun W => do
    withLocalDeclQ `instW .instImplicit q(SemiInnerProductSpace $K $W) fun instW => do
    withLocalDeclQ (u:=v) `w .default W fun w => do

    -- argFuns are selected arguments parametrized by `W`
    let argFunDecls :=
      mkLocalDecls argNames .default (← args.mapM fun arg => do mkArrow W (← inferType arg))

    withLocalDecls argFunDecls fun argFuns => do

      let argFunApps := argFuns.map (fun argFun => argFun.app w)

      let lhs ← 
        withLetDecls argNames argFunApps fun args' => do
          let xs' := Array.mergeSplit splitIds args' otherArgs
          let f ← mkLambdaFVars ((#[w] : Array Expr) ++ args') (mkAppN (← mkConst' constName) xs')
          mkAppM ``revCDeriv #[K,f]

      trace[Meta.generate_ftrans] "lhs for revCDeriv rule\n{← ppExpr lhs}"

      let argFunPropDecls ← 
        argFuns.mapM (fun argFun => do
          let name := (← argFun.fvarId!.getUserName).appendBefore "h"
          let bi : BinderInfo := .default
          let type ← mkAppM ``HasAdjDiff #[K,argFun]
          pure (name, bi, fun _ : Array Expr => pure (f:=TermElabM) type))

      withLocalDecls argFunPropDecls fun argFunProps => do

      let (rhs, proof) ← elabConvRewrite lhs conv

      trace[Meta.generate_ftrans] "rhs for revCDeriv rule\n{← ppExpr rhs}"

      let .lam _ _ b _ := rhs
        | throwError "transformed function should be in the form `fun w => ...` but got\n{← ppExpr rhs}"

      let b := b.instantiate1 w

      let transArgFuns ← argFuns.mapM (fun argFun => mkAppM ``revCDeriv #[K, argFun, w])

      let transArgNames := argNames.map (fun n => n.appendAfter "d" |>.appendAfter (toString n))
      let transArgFunDecls := 
        mkLocalDecls transArgNames .default (← liftM <| transArgFuns.mapM inferType)

      withLocalDecls transArgFunDecls fun transArgFunVars => do

      -- find all occurances of `<∂ (w':=w), argFunᵢ w` and replace it with recently introduced fvar
      let b' ← eliminateTransArgFun b argFuns transArgFuns transArgFunVars
      if b'.containsFVar w.fvarId! then
        throwError s!"transformed function {← ppExpr b'} still contains {← ppExpr w}"

      let idx ← firstExplicitNonTypeIdx xs

      let xs' := Array.mergeSplit splitIds transArgFunVars otherArgs
      let fvars := xs'[0:idx] ++ (#[W,instW] : Array Expr) ++ xs'[idx:]
      let transFun ← instantiateMVars (← mkLambdaFVars fvars b')
      let transFunName := constName.append argName |>.append "revCDeriv"
      trace[Meta.generate_ftrans] "generated revCDeriv function {transFunName}\n{← ppExpr transFun}"

      let transFunInfo : DefinitionVal := 
      {
        name  := transFunName
        type  := (← inferType transFun)
        value := transFun
        hints := .regular 0
        safety := .safe
        levelParams := vLvlName :: info.levelParams
      }

      addAndCompile (.defnDecl transFunInfo)

      let xs' := Array.mergeSplit splitIds argFuns otherArgs
      let fvars := xs'[0:idx] ++ (#[W, instW] : Array Expr) ++ xs'[idx:] ++ argFunProps
      let ruleProof ← instantiateMVars (← mkLambdaFVars fvars proof)
      let ruleName := constName.append argName |>.append "revCDeriv_rule"
      trace[Meta.generate_ftrans] "revCDeriv rule {ruleName}\n{← ppExpr (← inferType ruleProof)}"

      let ruleInfo : TheoremVal := 
      {
        name  := ruleName
        type  := (← inferType ruleProof)
        value := ruleProof
        levelParams := vLvlName :: info.levelParams
      }

      addDecl (.thmDecl ruleInfo)

      withLetDecls argNames transArgFuns fun transArgFunLets => do

        let xs' := Array.mergeSplit splitIds transArgFunLets otherArgs
        let fvars := xs'[0:idx] ++ (#[W,instW] : Array Expr) ++ xs'[idx:]
        let rhs ← 
          mkLambdaFVars 
            ((#[w] : Array Expr) ++ transArgFunLets) 
            (← mkAppOptM transFunName (fvars.map .some))

        let xs' := Array.mergeSplit splitIds argFuns otherArgs
        let fvars := xs'[0:idx] ++ (#[W, instW] : Array Expr) ++ xs'[idx:] ++ argFunProps
        let ruleDef ← instantiateMVars (← mkForallFVars fvars (← mkEq lhs rhs))
        let ruleDefName := constName.append argName |>.append "revCDeriv_rule_def"
        trace[Meta.generate_ftrans] "revCDeriv def rule {ruleDefName}\n{← ppExpr ruleDef}"

        let ruleDefInfo : TheoremVal := 
        {
          name  := ruleDefName
          type  := ruleDef
          value := ruleProof
          levelParams := vLvlName :: info.levelParams
        }

        addDecl (.thmDecl ruleDefInfo)


open Lean.Parser.Tactic.Conv in
syntax "#generate_revCDeriv" term num* " by " convSeq : command

elab_rules : command
| `(#generate_revCDeriv $fnStx $argIds:num* by $rw:convSeq) => do
  Command.liftTermElabM do
    let a := argIds.map (fun a => a.getNat)
    let fn ← elabTerm fnStx none
    let .some constName := fn.getAppFn'.constName?
      | throwError "unknown function {fnStx}"
    generateRevCDeriv constName a.toArraySet (← `(conv| ($rw)))


