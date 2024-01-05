import Std.Lean.Parser
import Mathlib.Tactic.NormNum.Core

import SciLean.Lean.Meta.Basic
import SciLean.Tactic.FTrans.Init
import SciLean.Tactic.FTrans.Simp
import SciLean.Tactic.LSimp2.Main
import SciLean.Tactic.StructuralInverse
import SciLean.Tactic.AnalyzeLambda

set_option linter.unusedVariables false

namespace SciLean.FTrans

open Lean Meta Qq

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
      trace[Meta.Tactic.ftrans.step] "case trivial let\n{← ppExpr e}"
      let body := body.swapBVars 0 1
      let e' := (.letE yName yType yValue (ext.replaceFTransFun e (.lam xName xType body xBi)) false)
      return .some (.visit { expr := e' })


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

-- ugh this is awful, clean this up!
def unfoldFunHead? (e : Expr) : SimpM (Option Expr) := do
  lambdaLetTelescope e fun xs b => do
    -- let b' ← whnfI b -- this screws things up for some reason :(
    -- if ¬(b==b') then
    --   trace[Meta.Tactic.ftrans.step] s!"unfolding \n`{← ppExpr b}`\n==>\n{← ppExpr b'}"
    --   mkLambdaFVars xs b'
    -- else 
    if let .some b' ← Tactic.LSimp.unfold? b then 
      trace[Meta.Tactic.ftrans.step] s!"unfolding \n`{← ppExpr b}`\n==>\n{← ppExpr b'}"
      mkLambdaFVars xs b'
    else if let .some b' ← withTransparency .instances <| unfoldDefinition? b then
      trace[Meta.Tactic.ftrans.step] s!"unfolding \n`{← ppExpr b}`\n==>\n{← ppExpr b'}"
      mkLambdaFVars xs b'
    else if let .some b' ← reduceRecMatcher? b then
      trace[Meta.Tactic.ftrans.step] s!"unfolding \n`{← ppExpr b}`\n==>\n{← ppExpr b'}"
      mkLambdaFVars xs b'
    else
      return none

/--
  Apply simp theorems marked with `ftrans`
-/
def constAppStep (e : Expr) (ftransName : Name) (ext : FTransExt) (funName : Name) 
  (noCandidatesCall : SimpM (Option Simp.Step)) -- return if there are no valid candidates
  : SimpM (Option Simp.Step) := do

  let candidates ← FTrans.getFTransRules funName ftransName

  if candidates.size ≠ 0 then
    trace[Meta.Tactic.ftrans.theorems] "applicable theorems: {candidates.map fun c => c.origin.key}"
    tryTheorems candidates ext.discharger e
  else
    trace[Meta.Tactic.ftrans.step] "no theorems associated to {funName}"
    noCandidatesCall


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
      let gType := (← inferType (.lam xName xType g bi)).bindingBody!
      if gType.hasLooseBVars then
        trace[Meta.Tactic.ftrans.step] "can't handle this bvar app case, unexpected dependency in type of {← ppExpr (.lam xName xType g bi)}"
        return none

      let h₁ := Expr.lam (xName.appendAfter "'") gType ((Expr.bvar 0).app x) bi
      let h₂ := Expr.lam xName xType g bi 
      ext.compRule e h₁ h₂

  | _ => return none


/-- Try to prove `FProp fun x => f x i` as composition `fun f => f i` `fun x => f x`
-/
def tryRemoveArg (e : Expr) (ext : FTransExt) (f : Expr) : SimpM (Option Simp.Step) := do
  match f with
  | .lam xName xType (.app g a) xBi => do

    if a.hasLooseBVars then 
      return none

    withLocalDecl xName xBi xType fun x => do
      let g := g.instantiate1 x

      let f' := Expr.lam `f (← inferType g) ((Expr.bvar 0).app a) default
      let g' ← mkLambdaFVars #[x] g

      ext.compRule e f' g'

  | _ => throwError "expected expression of the form `fun x => f x i`"


def piLetCase (e : Expr) (ftransName : Name) (ext : FTransExt) (f : Expr) 
  (ftrans : Expr → SimpM (Option Simp.Step)) 
  : SimpM (Option Simp.Step) := 
  match f with
  | .lam xName xType (.lam iName iType body iBi) xBi => 
    match body.consumeMData with
    | .letE yName yType yValue body _ => do
      let yType  := yType.consumeMData
      let yValue := yValue.consumeMData
      let body  := body.consumeMData
      -- We perform reduction because the type is quite often of the form 
      -- `(fun x => Y) #0` which is just `Y` 
      -- Usually this is caused by the usage of `FunLike`
      let yType := yType.headBeta

      -- we do not allow the type of `y` depend on `x` or `i`
      -- in particular, the following code we relies on the fact that the type of `y` does not depend on `i` 
      if (yType.hasLooseBVar 0) || (yType.hasLooseBVar 1) then
        throwError "dependent type encountered in pi let case"

      -- body does not depend on the let binding, thus we can get rid of it
      if ¬(body.hasLooseBVar 0) then
        let f' := Expr.lam xName xType (.lam iName iType (body.lowerLooseBVars 1 1) iBi) xBi
        let e' := ext.replaceFTransFun e f'
        trace[Meta.Tactic.ftrans.rewrite] "removing unused let\n{← ppExpr e}\n==>\n{← ppExpr e'}"
        return ← ftrans e'

      match (yValue.hasLooseBVar 1), (yValue.hasLooseBVar 0) with
      -- let y := constant
      | false, false => 
        let f' := Expr.lam xName xType (.lam iName iType (body.mapLooseBVarIds #[2,0,1].get?) iBi) xBi
        let e' := Expr.letE yName yType yValue (ext.replaceFTransFun e f') false
        trace[Meta.Tactic.ftrans.rewrite] "moving let out\n{← ppExpr e}\n==>\n{← ppExpr e'}"
        return .some (.visit {expr := e'})

      -- let y := g x
      | true, false => 
        let f' := Expr.lam iName iType (body.mapLooseBVarIds #[1,0,2].get?) iBi
        let f' := Expr.letE yName (yType.lowerLooseBVars 1 1) (yValue.lowerLooseBVars 1 1) f' false
        let f' := Expr.lam xName xType f' xBi
        trace[Meta.Tactic.ftrans.rewrite] "moving let out\n{← ppExpr f}\n==>\n{← ppExpr f'}"
        let e' := ext.replaceFTransFun e f'
        return ← ftrans e'

      -- let y := g i
      | false, true =>
        -- odd case I do not know how to handle
        throwError "can't handle this pi let case\n{← ppExpr e}"

      -- let y := g x i
      | true, true => 

        let g := Expr.lam xName xType (.lam iName iType yValue iBi) xBi

        -- body always depend on `y` otherwise we deal with it earlier
        match (body.hasLooseBVar 2), (body.hasLooseBVar 1) with
        -- let y := g x i; f y
        | false, false =>
          let f := 
            Expr.lam yName yType (binderInfo := default)
              (.lam iName iType (binderInfo := iBi)
                (body.mapLooseBVarIds #[1,0].get?))

            trace[Meta.Tactic.ftrans.step] "case `T fun x i => let y := g x i; f y` \n{← ppExpr e}"
            return ← ext.piElemWiseCompRule e f g

        -- T fun x i => let y := g x i; f y i
        | false, true => 
          -- right now there does not seem to be the need to distinguish between these two cases
          let f := 
            Expr.lam yName yType (binderInfo := default)
              (.lam iName iType (binderInfo := iBi)
                (body.mapLooseBVarIds #[1,0].get?))

          trace[Meta.Tactic.ftrans.step] "case `T fun x i => let y := g x i; f y i` \n{← ppExpr e}"
          return ← ext.piCompRule e f g

        -- let y := g x i; f x y
        -- let y := g x i; f x y i 
        | true, false | true, true => 
          -- right now there does not seem to be the need to distinguish between these two cases
          let f := 
            Expr.lam xName xType (binderInfo := xBi)
              (.lam yName yType (binderInfo := default)
                (.lam iName iType (binderInfo := iBi)
                  (body.mapLooseBVarIds #[1,0,2].get?)))

          trace[Meta.Tactic.ftrans.step] "case pi let\n{← ppExpr e}"
          return ← ext.piLetRule e f g

    | _ => throwError "expected expression of the form `fun x i => let y := g x i; f x y i`"
  | _ => throwError "expected expression of the form `fun x i => let y := g x i; f x y i`"


def piChangeOfVarsCase (e : Expr) (ftransName : Name) (ext : FTransExt) (f : Expr) (ftrans : Expr → SimpM (Option Simp.Step)) : SimpM (Option Simp.Step) := do
  match f with 
  | .lam xName xType (.lam iName iType body iBi) xBi => do
    withLocalDecl xName default xType fun x => do

      let g := (Expr.lam iName iType body iBi).instantiate1 x

      let (g',h') ← splitLambdaToComp g

      if (← isDefEq h' g') then
        return none

      trace[Meta.Tactic.ftrans.step] "case pi change of variables\n{← ppExpr e}\n{← ppExpr g'}\n{← ppExpr h'}"

      let .some (hinv, goals) ← structuralInverse h'
        | trace[Meta.Tactic.ftrans.step] "unable to invert {← ppExpr h'}"
          return none

      match hinv with
      | .full finv => 
        if (← isDefEq finv.invFun h') then
          return none
        else
          trace[Meta.Tactic.ftrans.step] "computed inverse {← ppExpr finv.invFun}"
          return ← ext.piInvRule e (← mkLambdaFVars #[x] g') finv
      | .right rinv => 
        trace[Meta.Tactic.ftrans.step] "computed right inverse {← ppExpr rinv.invFun}"
        return ← ext.piRInvRule e (← mkLambdaFVars #[x] g') rinv
  | _ => throwError "expected expression of the form `fun x i => f x i`"


private def peelOffBVarArgs (bvarId : Nat) (e : Expr) (n : Nat := 0) : Expr × Nat :=
  match e with
  | .app f x => 
    if x.hasLooseBVar bvarId then
      peelOffBVarArgs bvarId f (n+1)
    else 
      (.app f x, n)
  | e => (e, n)

/--
  This function is expecting expressions like:
  -- 1. bvar app - fun x i => f i.1 i.2.1 i.2.2
  -- 2. fvar app - fun x i => f x i.1 i.2.1 i.2.2   
 -/
def piBFVarAppCase (e : Expr) (ftransName : Name) (ext : FTransExt) (f : Expr) (ftrans : Expr → SimpM (Option Simp.Step)) : SimpM (Option Simp.Step) := do
  match f with 
  | .lam xName xType (.lam iName iType body iBi) xBi => do

    let fn := body.getAppFn
    if ¬(fn.isBVar || fn.isFVar) then
      throwError "expected expression of the form `fun x i => f x i` where head of `f` is bvar or fvar"

    withLocalDecl xName default xType fun x => do
      let g := (Expr.lam iName iType body iBi).instantiate1 x
      let .some (Is,Y) := (← inferType g).arrow?
       |  throwError "unexpected type {← inferType g} in pi bvar/fvar app case"

      let (body', n) := peelOffBVarArgs 0 body

      if body'.hasLooseBVar 0 then
        trace[Meta.Tactic.ftrans.step] "unable to curry back trailing arguments"
        return none

      let g := Expr.lam xName xType (body'.lowerLooseBVars 1 1) xBi
      return ← ext.piCurryNRule e g Is Y n 

  | _ => throwError "expected expression of the form `fun x i => f x i`"


def piConstAppCase (e : Expr) (ftransName : Name) (ext : FTransExt) (f : Expr) (ftrans : Expr → SimpM (Option Simp.Step)) : SimpM (Option Simp.Step) := do
  match f with 
  | .lam xName xType (.lam iName iType body iBi) xBi => do
    let fn := body.getAppFn
    if ¬(fn.isConst) then
      throwError "expected expression of the form `fun x i => f x i` where head of `f` is a constant"

    match fn with
    | .const constName _ =>
      match (← getEnv).find? constName with
      | none => return none
      | some info => 
        let constArity := info.type.forallArity
        let args := body.getAppArgs

        if args.size == constArity then

          let candidates ← FTrans.getFTransPiRules constName ftransName
          
          let step? ← tryTheorems candidates ext.discharger e

          match step? with
          | .some step => return step
          | none =>
            let (f',g') ← elemWiseSplitHighOrderLambdaToComp f

            if ¬(← isDefEq g' f) then
              return ← ext.piElemWiseCompRule e f' g'

        if args.size > constArity then
          let info ← analyzeLambda f
          if info.trailingArgCase == .trivialUncurried then
            let f' ← liftM <|
              withLocalDecl xName xBi xType fun x => do
                mkCurryFun info.trailingIds.size (f.app x).headBeta
                >>=
                mkLambdaFVars #[x]
            
            -- only proceed when curried `f` can be eta reduced
            -- that way we get rid of some trailing aguments
            -- if f' is not eta expanded then in the next step we would uncurry 
            -- it again and get into infinite looop
            if let .some f' := f'.etaExpanded? then

              let .some (_,Y') := (← inferType f).arrow? | return none
              let .some (_,Y) := Y'.arrow? | return none
  
              return ← ext.piCurryNRule e f' iType Y info.trailingIds.size

        return none

    | _ => throwError "expected expression of the form `fun x i => f x i` where head of `f` is a constant"
  | _ => throwError "expected expression of the form `fun x i => f x i`"


def piCase (e : Expr) (ftransName : Name) (ext : FTransExt) (f : Expr) (ftrans : Expr → SimpM (Option Simp.Step)) : SimpM (Option Simp.Step) := do
  if ¬ext.useRefinedPiRules then
    trace[Meta.Tactic.ftrans.step] "case pi\n{← ppExpr e}"
    ext.piRule e f 
  else
    match f with 
    | .lam xName xType (.lam iName iType body iBi) xBi => do

      -- If it does not depend on `i` then we apply `piConstRule`
      if ¬(body.hasLooseBVar 0) then
        trace[Meta.Tactic.ftrans.step] "case pi const\n{← ppExpr e}"
        let f' := .lam xName xType (body.lowerLooseBVars 1 1) xBi
        return ← ext.piConstRule e f' iType

      match body.consumeMData with
      | .app (.bvar 1) (.bvar 0) => 
        trace[Meta.Tactic.ftrans.step] "case pi id\n{← ppExpr e}"
        let .some (_,X) := xType.arrow? | return none
        return ← ext.piIdRule e X iType
      | .lam .. => 
        trace[Meta.Tactic.ftrans.step] "case pi uncurry\n{← ppExpr e}"
        ext.piUncurryRule e f
      | .letE .. => 
        piLetCase e ftransName ext f ftrans
      | body => 

        if body.isAppOfArity ``Prod.mk 4 then
          let g₁ := Expr.lam xName xType (.lam iName iType (body.getArg! 2) iBi) xBi
          let g₂ := Expr.lam xName xType (.lam iName iType (body.getArg! 3) iBi) xBi
          return ← ext.piProdRule e g₁ g₂

        -- eta reduction if possible
        if let .app f' (.bvar 0) := body then 
          if ¬(f'.hasLooseBVar 0) then
            let f' := Expr.lam xName xType (f'.lowerLooseBVars 1 1) xBi
            let e' := ext.replaceFTransFun e f'
            return ← ftrans e'

        let (f',g') ← splitHighOrderLambdaToComp f
        trace[Meta.Tactic.ftrans.step] "case pi comp\n{← ppExpr e}\n{← ppExpr f}\n{←ppExpr f'}\n{← isDefEq f' f}"
        trace[Meta.Tactic.ftrans.step] "{← ppExpr g'}"

        -- nontrivial split!
        if ¬(← isDefEq f' f) then
          return ← ext.compRule e f' g'

        if let .some step ← piChangeOfVarsCase e ftransName ext f ftrans then
          return step

        let fn := body.getAppFn
        
        if (fn.isBVar || fn.isFVar) then
          return ← piBFVarAppCase e ftransName ext f ftrans

        if (fn.isConst) then
          return ← piConstAppCase e ftransName ext f ftrans

        return none
    | _ => throwError "expected expression of the form `fun x i => f x i`"


/-- Try to apply function transformation to `e`. Returns `none` if expression is not a function transformation applied to a function.
  -/
partial def main (e : Expr) : SimpM (Option Simp.Step) := do

  let e := e.headBeta

  let .some (ftransName, ext, f) ← getFTrans? e
    | return none

  withTraceNode `ftrans (fun _ => do pure s!"ftrans") do

  let f := f.consumeMData

  match f with
  | .letE .. => letTelescope f λ xs b => do
    trace[Meta.Tactic.ftrans.step] "case let x := ..; ..\n{← ppExpr e}"
    let e' ← mkLetFVars xs (ext.replaceFTransFun e b)
    return .some (.visit { expr := e' })

  | .lam xName xType xBody xBi => 

    -- If it does not depend on `i` then we apply `constRule`
    if ¬(xBody.hasLooseBVar 0) then
      return ← ext.constRule e xType xBody

    match xBody.consumeMData.headBeta.consumeMData with
    | (.bvar 0) => 
      trace[Meta.Tactic.ftrans.step] "case id\n{← ppExpr e}"
      ext.idRule e xType 

    | .letE yName yType yValue body d => 
      let f' := Expr.lam xName xType (.letE yName yType yValue body d) xBi
      letCase e ftransName ext f'

    | .lam  .. => 
      piCase e ftransName ext f main

    -- | .mvar .. => return .some (.visit  {expr := ← instantiateMVars e})

    | xBody => do
      let f' := Expr.lam xName xType xBody xBi
      let g := xBody.getAppFn'
      match g with 
      | .fvar .. => 
        trace[Meta.Tactic.ftrans.step] "case fvar app `{← ppExpr g}`\n{← ppExpr e}"
        fvarAppStep e ext f'
      | .bvar .. => 
        trace[Meta.Tactic.ftrans.step] "case bvar app\n{← ppExpr e}"
        bvarAppStep e ext f'
      | .proj typeName idx _ => do
        let .some info := getStructureInfo? (← getEnv) typeName | return none
        let .some projName :=info.getProjFn? idx | return none
        constAppStep e ftransName ext projName (pure none)
      | .const funName _ =>
        let numArgs := xBody.getAppNumArgs
        let arity ← getConstArity funName
        if numArgs > arity then
          trace[Meta.Tactic.ftrans.step] s!"const app step, tring projection rule as number of arguments({numArgs}) is bigger then constant's({funName}) arity ({arity})"
          let .some step ← tryRemoveArg e ext f' | pure ()
          return step

        trace[Meta.Tactic.ftrans.step] "case const app `{funName}`.\n{← ppExpr e}"
        constAppStep e ftransName ext funName 
          (do -- no candidates call
            let .some f'' ← unfoldFunHead? f' | return none
            let e' := ext.replaceFTransFun e f''
            let step : Simp.Step := .visit { expr := e' }
            Simp.andThen step main)

        | _ => 
          trace[Meta.Tactic.ftrans.step] "unknown case, app function constructor: {g.ctorName}\n{← ppExpr e}\n"
          return none

  -- | .mvar _ => do
  --   return .some (.visit  {expr :=← instantiateMVars e})
  | .proj typeName idx _ => do
    let .some info := getStructureInfo? (← getEnv) typeName | return none
    let .some projName :=info.getProjFn? idx | return none
    constAppStep e ftransName ext projName (pure none)

  | f => 
    match f.getAppFn.consumeMData with
    | .const funName _ => 
      trace[Meta.Tactic.ftrans.step] "case const app `{funName}`.\n{← ppExpr e}"
      constAppStep e ftransName ext funName 
        (do -- no candidates call
          let .some f'' ← unfoldFunHead? f | return none
          let e' := ext.replaceFTransFun e f''
          let step : Simp.Step := .visit { expr := e' }
          Simp.andThen step main)

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


namespace CustomPrePost

open Lean.Meta.Simp in
def _root_.Lean.Meta.Simp.Result.then (r r' : Result) : MetaM Result := do
  match r.proof?, r'.proof? with
  | .some p, .some p' => return { expr := r'.expr, proof? := .some (← mkEqTrans p p') }
  | .some p, .none => return { expr := r'.expr, proof? := .some p }
  | .none, _ => return r'

open Lean.Meta.Simp in
/-- Keep on rewriting if possible unlike `Lean.Meta.Simp.rewritePre` -/
def rewritePre (e : Expr) (discharge? : Expr → SimpM (Option Expr)) (rflOnly := false) : SimpM Step := do
  let mut cont := true
  let mut r : Result := {expr := e}
  while cont do
    cont := false
    for thms in (← read).simpTheorems do
      if let some r' ← rewrite? r.expr thms.pre thms.erased discharge? (tag := "pre") (rflOnly := rflOnly) then
        r ← r.then r'
        cont := true
        break
  return .visit r

open Lean.Meta.Simp in
/-- Keep on rewriting if possible unlike `Lean.Meta.Simp.rewritePre` -/
def rewritePost (e : Expr) (discharge? : Expr → SimpM (Option Expr)) (rflOnly := false) : SimpM Step := do
  let mut cont := true
  let mut r : Result := {expr := e}
  while cont do
    cont := false
    for thms in (← read).simpTheorems do
      if let some r' ← rewrite? r.expr thms.post thms.erased discharge? (tag := "post") (rflOnly := rflOnly) then
        r ← r.then r'
        cont := true
        break
  return .visit r

open Lean.Meta.Simp in
def pre (e : Expr) (discharge? : Expr → SimpM (Option Expr)) : SimpM Step := do
  let s ← rewritePre e discharge?
  andThen s tryRewriteUsingDecide?

open Lean.Meta.Simp in
def post (e : Expr) (discharge? : Expr → SimpM (Option Expr)) : SimpM Step := do
  let s ← rewritePost e discharge?
  let s ← andThen s (simpMatch? discharge?)
  let s ← andThen s simpArith?
  let s ← andThen s tryRewriteUsingDecide?
  andThen s tryRewriteCtorEq?

namespace CustomPrePost


variable (ctx : Simp.Context) (useSimp := true) in
mutual
  -- This custom discharger is a residue of the code for `norm_num`
  -- It is probably useless and the code can be simplified
  partial def discharge (e : Expr) : SimpM (Option Expr) := do (← deriveSimp e).ofTrue

  partial def methods : Simp.Methods :=
    if useSimp then {
      pre  := fun e ↦ do
        Simp.andThen (← withTraceNode `lsimp (fun _ => do pure s!"lsimp default pre") do CustomPrePost.pre e discharge) (fun e' => tryFTrans? e' discharge)
      post := fun e ↦ do
        Simp.andThen (← withTraceNode `lsimp (fun _ => do pure s!"lsimp default post") do CustomPrePost.post e discharge) (fun e' => tryFTrans? e' discharge (post := true))
      discharge? := discharge
    } else {
      pre  := fun e ↦ do 
        Simp.andThen (.visit { expr := e }) (fun e' => tryFTrans? e' discharge)
      post := fun e ↦ do
        Simp.andThen (.visit { expr := e }) (fun e' => tryFTrans? e' discharge (post := true))
      discharge? := discharge
    }

  partial def deriveSimp (e : Expr) : MetaM Simp.Result := do
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

def getFTransTheorems : CoreM SimpTheorems := do
  let ext ← Lean.Meta.getSimpExtension? "ftrans_simp"
  ext.get!.getTheorems

/-- Constructs a simp context from the simp argument syntax. -/
def getFTransContext (args : Syntax) (simpOnly := false) :
    TacticM Simp.Context := do
  let simpTheorems ←
    if simpOnly then simpOnlyBuiltins.foldlM (·.addConst ·) {} else getFTransTheorems
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
  let ctx ← getFTransContext args (!useSimp || simpOnly)
  let ctx := {ctx with config := {ctx.config with iota := true, zeta := false, singlePass := true, dsimp := false, decide := false}}
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
  let ctx ← getFTransContext stx[2] !stx[1].isNone
  let ctx := {ctx with config := {ctx.config with iota := true, zeta := false, singlePass := true, dsimp := false, decide := false}}
  Conv.applySimpResult (← deriveSimp ctx (← instantiateMVars (← Conv.getLhs)) (useSimp := true))
