import SciLean.Tactic.FProp.Init

open Lean Meta Qq

namespace SciLean.FProp

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

set_option linter.unusedVariables false in
def bvarAppCase (e : Expr) (fpropName : Name) (ext : FPropExt) (f : Expr) : FPropM (Option Expr) := do

  let .lam n t (.app g x) bi := f
    | trace[Meta.Tactic.fprop.step] "bvar app case can't handle functions like {← ppExpr f}"
      return none

  if x.hasLooseBVars then
    trace[Meta.Tactic.fprop.step] "bvar app case can't handle functions like {← ppExpr f}"
    return none
  
  if g == .bvar 0 then
    ext.projRule e
  else
    let g := .lam n t g bi
    let gType ← inferType g
    let fType := gType.getForallBody
    if fType.hasLooseBVars then
      trace[Meta.Tactic.fprop.step] "bvar app step can't handle dependent functions of type {← ppExpr fType} appearing in {← ppExpr f}"
      return none

    let h := .lam n fType ((Expr.bvar 0).app x) bi
    ext.compRule e h g


def cache (e : Expr) (proof? : Option Expr) : FPropM (Option Expr) := -- return proof?
  match proof? with
  | .none => return none
  | .some proof => do
    modify (fun s => { s with cache := s.cache.insert e { expr := q(True), proof? := proof} })
    return proof


def getLocalRules (fpropName : Name) : MetaM (Array SimpTheorem) := do
  let mut arr : Array SimpTheorem := #[]

  let lctx ← getLCtx
  for var in lctx do
    let type ← instantiateMVars var.type
    
    if (type.getForallBody.getAppFn.constName? == .some fpropName) &&
       (var.kind ≠ Lean.LocalDeclKind.auxDecl) then
       arr := arr.push {
         proof := var.toExpr
         origin := .fvar var.fvarId
         rfl := false
       }

  return arr

-- returns proof of expression like given expression like `Differentiable K fun x => f x`
mutual 
  partial def fprop (e : Expr) : FPropM (Option Expr) := do

    -- this is for testing whether mdata cause problems or not
    -- let e := e.purgeMData

    if let .some { expr := _, proof? := .some proof } := (← get).cache.find? e then
      trace[Meta.Tactic.fprop.cache] "cached result for {e}"
      return proof
    else
      match e with
      | .letE .. => 
        letTelescope e fun xs b => do
          let .some proof ← fprop b
            | return none
          cache e (← mkLambdaFVars xs proof)
      | .forallE .. => 
        forallTelescope e fun xs b => do
          let .some proof ← fprop b
            | return none
          cache e (← mkLambdaFVars xs proof)
      | .mdata _ e' => fprop e'
      | .mvar _ => instantiateMVars e >>= fprop
      | _ => 
        let .some proof ← main e
          | return none
        cache e proof
        

  partial def main (e : Expr) : FPropM (Option Expr) := do

    let .some (fpropName, ext, f) ← getFProp? e
      | return none

    match f.consumeMData with
    | .letE .. => letTelescope f fun xs b => do 
      trace[Meta.Tactic.fprop.step] "case let x := ..; ..\n{← ppExpr e}"
      let e' := ext.replaceFPropFun e b
      fprop (← mkLambdaFVars xs e')

    | .lam xName xType xBody xBi => 

      match xBody.consumeMData.headBeta.consumeMData with
      | (.bvar 0) => 
        trace[Meta.Tactic.fprop.step] "case id\n{← ppExpr e}"
        ext.identityRule e

      | .letE yName yType yValue yBody _ => 
        let yType  := yType.consumeMData
        let yValue := yValue.consumeMData
        let yBody  := yBody.consumeMData
        -- We perform reduction because the type is quite often of the form 
        -- `(fun x => Y) #0` which is just `Y` 
        -- Usually this is caused by the usage of `FunLike`
        let yType := yType.headBeta
        if (yType.hasLooseBVar 0) then
          throwError "dependent type encountered {← ppExpr (Expr.forallE xName xType yType default)}"

        if ¬(yValue.hasLooseBVar 0) then
          let body := yBody.swapBVars 0 1
          let e' := (.letE yName yType yValue (ext.replaceFPropFun e (.lam xName xType body xBi)) false)
          return ← FProp.fprop e'

        match (yBody.hasLooseBVar 0), (yBody.hasLooseBVar 1) with
        | true, true =>
          trace[Meta.Tactic.fprop.step] "case let\n{← ppExpr e}"
          let f := Expr.lam xName xType (.lam yName yType yBody default) xBi
          let g := Expr.lam xName xType yValue default
          ext.lambdaLetRule e f g

        | true, false => 
          trace[Meta.Tactic.fprop.step] "case let simple\n{← ppExpr e}"
          let f := Expr.lam yName yType yBody default
          let g := Expr.lam xName xType yValue default
          ext.compRule e f g

        | false, _ => 
          let f := Expr.lam xName xType (yBody.lowerLooseBVars 1 1) xBi
          FProp.fprop (ext.replaceFPropFun e f)

      | .lam  .. => 
        trace[Meta.Tactic.fprop.step] "case pi\n{← ppExpr e}"
        ext.lambdaLambdaRule e f

      | .mvar .. => fprop (← instantiateMVars e)

      | xBody => do
        if !(xBody.hasLooseBVar 0) then
          trace[Meta.Tactic.fprop.step] "case const\n{← ppExpr e}"
          ext.constantRule e
        else 
          let xBody' := xBody
          let f' := Expr.lam xName xType xBody' xBi
          let g := xBody'.getAppFn'

          match g with 
          | .fvar .. => 
            trace[Meta.Tactic.fprop.step] "case fvar app `{← ppExpr g}`\n{← ppExpr e}"
            fvarAppCase e fpropName ext f'
          | .bvar .. => 
            trace[Meta.Tactic.fprop.step] "case bvar app\n{← ppExpr e}"
            bvarAppCase e fpropName ext f'
          | .const funName _ =>
            trace[Meta.Tactic.fprop.step] "case const app `{← ppExpr g}`.\n{← ppExpr e}"
            constAppCase e fpropName ext funName
          | _ => 
            trace[Meta.Tactic.fprop.step] "unknown case, app function constructor: {g.ctorName}\n{← ppExpr e}\n"
            tryLocalTheorems e fpropName ext

    | .mvar _ => do
      fprop (← instantiateMVars e)

    | f => 
      match f.getAppFn.consumeMData with
      | .const funName _ =>
        trace[Meta.Tactic.fprop.step] "case const app `{funName}.\n{← ppExpr e}"
        constAppCase e fpropName ext funName
      | _ => 
        trace[Meta.Tactic.fprop.step] "unknown case, expression constructor: {f.ctorName}\n{← ppExpr e}\n"
        tryLocalTheorems e fpropName ext

  partial def fvarAppCase (e : Expr) (fpropName : Name) (ext : FPropExt) (f : Expr) : FPropM (Option Expr) := do
    let (f', g') ← splitLambdaToComp f

    -- trivial case, this prevents an infinite loop
    if (← isDefEq f' f) then
      trace[Meta.Tactic.fprop.step] "fvar app case: trivial"
      tryLocalTheorems e fpropName ext
    else
      trace[Meta.Tactic.fprop.step] "fvar app case: decomposed into `({← ppExpr f'}) ∘ ({← ppExpr g'})`"
      ext.compRule e f' g'

  partial def constAppCase (e : Expr) (fpropName : Name) (ext : FPropExt) (funName : Name) : FPropM (Option Expr) := do

    let candidates ← FProp.getFPropRules funName fpropName

    if candidates.size = 0 then
      trace[Meta.Tactic.fprop.apply] "no suitable theorems found for {← ppExpr e}"

    for thm in candidates do
      if let some proof ← tryTheorem? e thm ext.discharger then
        return proof

    -- if all fails try local rules
    tryLocalTheorems e fpropName ext

  partial def tryLocalTheorems (e : Expr) (fpropName : Name) (ext : FPropExt) : FPropM (Option Expr) := do

    let candidates ← getLocalRules fpropName

    for thm in candidates do
      if let some proof ← tryTheorem? e thm ext.discharger then
        return proof

    return none

  partial def synthesizeInstance (thmId : Origin) (x type : Expr) : MetaM Bool := do
    match (← trySynthInstance type) with
    | LOption.some val =>
      -- if (← withReducibleAndInstances <| isDefEq x val) then
      if (← withReducibleAndInstances <| isDefEq x val) then
        return true
      else
        trace[Meta.Tactic.fprop.discharge] "{← ppOrigin thmId}, failed to assign instance{indentExpr type}\nsythesized value{indentExpr val}\nis not definitionally equal to{indentExpr x}"
        return false
    | _ =>
      trace[Meta.Tactic.fprop.discharge] "{← ppOrigin thmId}, failed to synthesize instance{indentExpr type}"
      return false

  partial def synthesizeArgs (thmId : Origin) (xs : Array Expr) (bis : Array BinderInfo) (discharge? : Expr → FPropM (Option Expr)) : FPropM Bool := do
        for x in xs, bi in bis do
          let type ← inferType x
          if bi.isInstImplicit then
            unless (← synthesizeInstance thmId x type) do
              return false
          else if (← instantiateMVars x).isMVar then

            -- try type class
            if (← isClass? type).isSome then
              if (← synthesizeInstance thmId x type) then
                continue

            -- try function property
            if (← getFProp? type.getForallBody).isSome then
              if let .some proof ← fprop (← instantiateMVars type) then
                if (← isDefEq x proof) then
                  continue
                else do
                  trace[Meta.Tactic.fprop.discharge] "{← ppOrigin thmId}, failed to assign proof{indentExpr type}"
                  return false

            -- try discharger
            if (← isProp type) then
              if let .some proof ← discharge? type then
                if (← isDefEq x proof) then
                  continue 
                else do
                  trace[Meta.Tactic.fprop.discharge] "{← ppOrigin thmId}, failed to assign proof{indentExpr type}"
                  return false

            trace[Meta.Tactic.fprop.discharge] "{← ppOrigin thmId}, failed to discharge hypotheses{indentExpr type}"
            return false

        return true

  partial def tryTheoremCore (xs : Array Expr) (bis : Array BinderInfo) (val : Expr) (type : Expr) (e : Expr) (thm : SimpTheorem) (discharge? : Expr → FPropM (Option Expr)) : FPropM (Option Expr) := do
      if (← isDefEq type e) then
        unless (← synthesizeArgs thm.origin xs bis discharge?) do
          return none
        let proof ← instantiateMVars (mkAppN val xs)
        if (← hasAssignableMVar proof) then
          trace[Meta.Tactic.fprop.apply] "{← ppSimpTheorem thm}, has unassigned metavariables after unification"
          return none
        trace[Meta.Tactic.fprop.apply] "{← ppSimpTheorem thm}, \n{e}"
        return proof
      else
        trace[Meta.Tactic.fprop.unify] "failed to unify\n{type}\nwith\n{e}"
        return none

  partial def tryTheorem? (e : Expr) (thm : SimpTheorem) (discharge? : Expr → FPropM (Option Expr)) : FPropM (Option Expr) := do
    withNewMCtxDepth do
      let val  ← thm.getValue
      let type ← instantiateMVars (← inferType val)
      let (xs, bis, type) ← forallMetaTelescope type
      let type ← instantiateMVars type
      tryTheoremCore xs bis val type e thm discharge?
end

