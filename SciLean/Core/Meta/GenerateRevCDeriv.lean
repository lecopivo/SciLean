import SciLean.Core.Objects.FinVec
import SciLean.Core.FunctionTransformations
import SciLean.Core.Notation

namespace SciLean.Meta

open Lean Meta Qq

def isTypeQ (e : Expr) : MetaM (Option ((u : Level) × Q(Type $u))) := do
  let u ← mkFreshLevelMVar
  let .some e ← checkTypeQ e q(Type $u)
    | return none
  return .some ⟨u, e⟩

/-- Returns `(id, u, K)` where `K` is infered field type with universe level `u`

The index `id` tells that arguments `args[id:]` have already `K` in its local context with valid `IsROrC K` instances. -/
def getFieldOutOfContextQ (args : Array Expr) : MetaM (Option ((u : Level) × Q(Type $u))) := do

  for arg in args do
    let type ← inferType arg

    if type.isAppOf ``IsROrC then
      return ← isTypeQ (type.getArg! 0)

    if type.isAppOf ``Scalar then
      return ← isTypeQ (type.getArg! 1)

    if type.isAppOf ``RealScalar then
      return ← isTypeQ (type.getArg! 0)

    if type.isAppOf ``Vec then
      return ← isTypeQ (type.getArg! 0)

    if type.isAppOf ``SemiInnerProductSpace then
      return ← isTypeQ (type.getArg! 0)

    if type.isAppOf ``SemiHilbert then
      return ← isTypeQ (type.getArg! 0)

    if type.isAppOf ``FinVec then
      return ← isTypeQ (type.getArg! 1)

  return none

def firstExplicitNonTypeIdx (xs : Array Expr) : MetaM Nat := do
  let mut i := 0
  for x in xs do
    let X ← inferType x
    if (← x.fvarId!.getBinderInfo) == .default && 
       ¬X.bindingBodyRec.isType then
      return i
    i := i + 1
  return i


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
          IO.println s!"replacing {← ppExpr x} with {← ppExpr transArgFunVars[i]!}"
          pure (.yield transArgFunVars[i]!)
        else 
          pure .noMatch)

  IO.println s!"transformed function with arguments eliminated succesfully \n{← ppExpr e'}"

  if let .some i := argFuns.findIdx? (fun argFun => e'.containsFVar argFun.fvarId!) then
    throwError "Failed to elimate {← ppExpr argFuns[i]!} out of transformed function{←ppExpr e}\n it is expected that {← ppExpr argFuns[i]!} appears only in {← ppExpr transArgFuns[i]!}"

  return e'


def generateRevCDeriv (constName : Name) (argIds : ArraySet Nat) : MetaM Unit := do
  let info ← getConstInfoDefn constName

  forallTelescope info.type fun xs type => do

    let (args, otherArgs, splitIds) := xs.splitIdx (fun i _ => i.1 ∈ argIds)

    IO.println s!"arguments {← args.mapM fun arg => do pure s!"({←ppExpr arg} : {← ppExpr (← inferType arg)})"}"

    let .some ⟨u,K⟩ ← getFieldOutOfContextQ xs
      | throwError "unable to figure out what is the field"

    IO.println s!"detected field {← ppExpr K}"

    let _isROrC ← synthInstanceQ q(IsROrC $K)

    -- check that return type form SemiInnerProductSpace
    let .some _semiInnerProductSpace ← synthInstance? (← mkAppM ``SemiInnerProductSpace #[K, type])
      | throwError "unable to synthesize `SemiInnerProductSpace` for the return type {← ppExpr type}"

    -- check that all arguments form SemiInnerProductSpace
    for arg in args do
      let argType ← inferType arg
      let .some _semiInnerProductSpace ← synthInstance? (← mkAppM ``SemiInnerProductSpace #[K, argType])
        | throwError "unable to synthesize `SemiInnerProductSpace {← ppExpr K} {← ppExpr argType}` for the argument {← ppExpr arg}"
      
    IO.println "all necessary types form SemiInnerProductSpace!"

    -- check for dependent types
    for x in xs do
      let X ← inferType x
      if let .some arg := args.find? (fun arg => X.containsFVar arg.fvarId!) then
        throwError s!"argument ({← ppExpr x} : {← inferType x >>= ppExpr}) depends on the argument {← ppExpr arg}, dependent types like this are not supported"

    -- let vLvlName := `v
    -- let v ← mkFreshLevelMVar
    -- let v := Level.param vLvlName
    withLocalDeclQ `W .implicit q(Type) fun W => do
    withLocalDeclQ `instW .instImplicit q(SemiInnerProductSpace $K $W) fun instW => do
    withLocalDeclQ (u:=levelOne) `w .default W fun w => do

      -- argFuns are selected arguments parametrized by `W`
      let argFunDecls ← 
        args.mapM (fun arg => do
          let name ← arg.fvarId!.getUserName
          let bi : BinderInfo := .default
          let type ← mkArrow W (← inferType arg)
          pure (name, bi, fun _ : Array Expr => pure (f:=MetaM) type))

      withLocalDecls argFunDecls fun argFuns => do

        let argFunApps := argFuns.map (fun argFun => argFun.app w)

        let xs' := Array.mergeSplit splitIds argFunApps otherArgs

        let f ← mkLambdaFVars #[w] (mkAppN (← mkConst' constName) xs')
        let lhs ← mkAppM ``revCDeriv #[K,f]

        let argFunPropDecls ← 
          argFuns.mapM (fun argFun => do
            let name := (← argFun.fvarId!.getUserName).appendBefore "h"
            let bi : BinderInfo := .default
            let type ← mkAppM ``HasAdjDiff #[K,argFun]
            pure (name, bi, fun _ : Array Expr => pure (f:=MetaM) type))

        withLocalDecls argFunPropDecls fun argFunProps => do

          let constId := mkIdent constName
          let (rhs, proof) ← rewriteByConv lhs (← `(conv| (unfold $constId; autodiff)))

          IO.println s!"lhs: {← ppExpr lhs}"
          IO.println s!"rhs: {← ppExpr rhs}"

          if ¬(← isDefEq (← mkEq lhs rhs) (← inferType proof)) then
            throwError "generated proof is not type correct, expected proof of\n{← ppExpr (← mkEq lhs rhs)}\nbut got proof of\n{← ppExpr (← inferType proof)}"

          if let .lam _ _ b _ := rhs then
            let b := b.instantiate1 w

            let transArgFuns ← argFuns.mapM (fun argFun => mkAppM ``revCDeriv #[K, argFun, w])

            let transArgFunDecls ←
              argFuns.mapIdxM (fun i argFun => do
                let name := (← argFun.fvarId!.getUserName)
                let bi : BinderInfo := .default
                let type ← inferType transArgFuns[i]!
                pure (name, bi, fun _ : Array Expr => pure (f:=MetaM) type))

            withLocalDecls transArgFunDecls fun transArgFunVars => do

              -- find all occurances of `<∂ (w':=w), argFunᵢ w` and replace it with recently introduced fvar
              let b' ← eliminateTransArgFun b argFuns transArgFuns transArgFunVars
              if b'.containsFVar w.fvarId! then
                throwError s!"transformed function {← ppExpr b'} still contains {← ppExpr w}"

              let idx ← firstExplicitNonTypeIdx xs

              let xs' := Array.mergeSplit splitIds transArgFunVars otherArgs
              let fvars := xs'[0:idx] ++ (#[W,instW] : Array Expr) ++ xs'[idx:]
              let transFun ← instantiateMVars (← mkLambdaFVars fvars b')
              let transFunName := constName.append "arg_" |>.append "revCDeriv"
              IO.println s!"revCDeriv def fun\n{← ppExpr transFun}"

              let transFunInfo : DefinitionVal := 
              {
                name  := transFunName
                type  := (← inferType transFun)
                value := transFun
                hints := .regular 0
                safety := .safe
                levelParams := info.levelParams
              }

              addAndCompile (.defnDecl transFunInfo)


              let xs' := Array.mergeSplit splitIds argFuns otherArgs
              let fvars := xs'[0:idx] ++ (#[W, instW] : Array Expr) ++ xs'[idx:] ++ argFunProps
              let ruleProof ← instantiateMVars (← mkLambdaFVars fvars proof)
              let ruleName := constName.append "arg_" |>.append "revCDeriv_rule"
              IO.println s!"revCDeriv rule\n{← ppExpr (← inferType ruleProof)}"

              let ruleInfo : TheoremVal := 
              {
                name  := ruleName
                type  := (← inferType ruleProof)
                value := ruleProof
                levelParams := info.levelParams
              }

              addDecl (.thmDecl ruleInfo)
              
              -- turn ftransArgFunVars to let bindings
              let mut lctx ← getLCtx
              for transArgFunVar in transArgFunVars, transArgFun in transArgFuns do
                lctx := lctx.modifyLocalDecl transArgFunVar.fvarId!
                  fun decl => 
                    match decl with
                    | .cdecl index fvarId userName type _ kind =>
                      .ldecl index fvarId userName type transArgFun false kind
                    | _ => unreachable!

              withLCtx lctx (← getLocalInstances) do

                let xs' := Array.mergeSplit splitIds transArgFunVars otherArgs
                let fvars := xs'[0:idx] ++ (#[W,instW] : Array Expr) ++ xs'[idx:]
                -- TODO: !!!replace transformedFun with new declaration!!!
                let rhs ← mkLambdaFVars ((#[w] : Array Expr) ++ transArgFunVars) (← mkAppOptM transFunName (fvars.map .some))
                  
                let xs' := Array.mergeSplit splitIds argFuns otherArgs
                let fvars := xs'[0:idx] ++ (#[W, instW] : Array Expr) ++ xs'[idx:] ++ argFunProps
                let ruleDef ← instantiateMVars (← mkForallFVars fvars (← mkEq lhs rhs))
                let ruleDefName := constName.append "arg_" |>.append "revCDeriv_rule_def"
                IO.println s!"revCDeriv rule def\n{← ppExpr ruleDef}"

                let ruleDefInfo : TheoremVal := 
                {
                  name  := ruleDefName
                  type  := ruleDef
                  value := ruleProof
                  levelParams := info.levelParams
                }

                addDecl (.thmDecl ruleDefInfo)

                pure ()

            pure ()
          else
            throwError "transformed function should be in the form `fun w => ...` but got\n{← ppExpr rhs}"
          pure ()


def mymul {K : Type} [IsROrC K] (x y : K) := x * y


variable {K : Type} [IsROrC K] {W : Type v} [SemiInnerProductSpace K W]

set_default_scalar K


set_option trace.Meta.Tactic.fprop.discharge true in
set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.simp.unify true in
example (x y : W → K) (hx : HasAdjDiff K x) (hy : HasAdjDiff K y)
  : (<∂ w, mymul (x w) (y w))
    =
    sorry :=
by
  unfold mymul
  ftrans only
#exit

set_option pp.funBinderTypes true in
-- set_option trace.Meta.Tactic.ftrans.step true in
-- set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.fprop.discharge true in
set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.simp.unify true in
set_option trace.Meta.Tactic.ftrans.step true in
#eval show MetaM Unit from do

  -- generateRevCDeriv ``norm2 #[4].toArraySet
  generateRevCDeriv ``mymul #[2,3].toArraySet



#print mymul.arg_.revCDeriv
#check mymul.arg_.revCDeriv_rule
#check mymul.arg_.revCDeriv_rule_def
