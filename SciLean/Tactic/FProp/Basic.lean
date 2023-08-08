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

def applyBVarApp (e : Expr) : FPropM (Option Expr) := do
  let .some (_, ext, F) ← getFProp? e
    | return none

  let .lam n t (.app f x) bi := F
    | trace[Meta.Tactic.fprop.step] "bvar app step can't handle functions like {← ppExpr F}"
      return none

  if x.hasLooseBVars then
    trace[Meta.Tactic.fprop.step] "bvar app step can't handle functions like {← ppExpr F}"
    return none

  
  if f == .bvar 0 then
    ext.projRule e
  else
    let g := .lam n t f bi
    let gType ← inferType g
    let fType := gType.getForallBody
    if fType.hasLooseBVars then
      trace[Meta.Tactic.fprop.step] "bvar app step can't handle dependent functions of type {← ppExpr fType} appearing in {← ppExpr F}"
      return none

    let h := .lam n fType  ((Expr.bvar 0).app x) bi
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

    let e ← instantiateMVars e

    if let .some { expr := _, proof? := .some proof } := (← get).cache.find? e then
      trace[Meta.Tactic.fprop.cache] "cached result for {e}"
      return proof
    else
      if e.isLet then
        letTelescope e fun xs b => do
          let .some proof ← main b
            | return none
          cache e (← mkLambdaFVars xs proof)
      else 
        forallTelescope e fun xs b => do
          let .some proof ← main b
            | return none
          cache e (← mkLambdaFVars xs proof)

  partial def main (e : Expr) : FPropM (Option Expr) := do

    let .some (_, ext, f) ← getFProp? e
      | return none

    match f with
    | .letE .. => letTelescope f fun xs b => do 
      trace[Meta.Tactic.fprop.step] "case let x := ..; ..\n{← ppExpr e}"
      let e' := ext.replaceFPropFun e b
      fprop (← mkLambdaFVars xs e')

    | .lam _ _ (.bvar  0) _ => 
      trace[Meta.Tactic.fprop.step] "case id\n{← ppExpr e}"
      ext.identityRule e

    | .lam xName xType (.letE yName yType yValue body _) xBi => 
      -- We perform reduction because the type is quite often of the form 
      -- `(fun x => Y) #0` which is just `Y`
      let yType := yType.headBeta
      if (yType.hasLooseBVar 0) then
        throwError "dependent type encountered {← ppExpr (Expr.forallE xName xType yType default)}"

      match (body.hasLooseBVar 0), (body.hasLooseBVar 1) with
      | true, true =>
        trace[Meta.Tactic.fprop.step] "case let\n{← ppExpr e}"
        let f := Expr.lam xName xType (.lam yName yType body default) xBi
        let g := Expr.lam xName xType yValue default
        ext.lambdaLetRule e f g

      | true, false => 
        trace[Meta.Tactic.fprop.step] "case comp\n{← ppExpr e}"
        let f := Expr.lam yName yType body default
        let g := Expr.lam xName xType yValue default
        ext.compRule e f g

      | false, _ => 
        let f := Expr.lam xName xType (body.lowerLooseBVars 1 1) xBi
        FProp.fprop (ext.replaceFPropFun e f)


    | .lam _ _ (.lam  ..) _ => 
      trace[Meta.Tactic.fprop.step] "case pi\n{← ppExpr e}"
      ext.lambdaLambdaRule e f

    | .lam _ _ b _ => do
      if !(b.hasLooseBVar 0) then
        trace[Meta.Tactic.fprop.step] "case const\n{← ppExpr e}"
        ext.constantRule e
      else if b.getAppFn.isFVar then
        trace[Meta.Tactic.fprop.step] "case fvar app\n{← ppExpr e}"
        applyFVarApp e ext.discharger
      else if b.getAppFn.isBVar then
        trace[Meta.Tactic.fprop.step] "case bvar app\n{← ppExpr e}"
        applyBVarApp e
      else
        trace[Meta.Tactic.fprop.step] "case other\n{← ppExpr e}\n"
        applyTheorems e (ext.discharger)

    | .mvar _ => do
      fprop (← instantiateMVars e)

    | _ => do
      trace[Meta.Tactic.fprop.step] "case other\n{← ppExpr e}\n"
      applyTheorems e (ext.discharger)

  partial def applyFVarApp (e : Expr) (discharge? : Expr → FPropM (Option Expr)) : FPropM (Option Expr) := do
    let .some (_, ext, F) ← getFProp? e
      | return none

    if ¬F.isLambda then
      applyTheorems e discharge?
    else
      let (f, g) ← splitLambdaToComp F

      -- trivial case and prevent infinite loop
      if (← isDefEq f F) then
        trace[Meta.Tactic.fprop.step] "fvar app case: trivial"

        applyTheorems e discharge?
      else

        trace[Meta.Tactic.fprop.step] "fvar app case: decomposed into `({← ppExpr f}) ∘ ({← ppExpr g})`"
        ext.compRule e f g

  partial def applyTheorems (e : Expr) (discharge? : Expr → FPropM (Option Expr)) : FPropM (Option Expr) := do
    let .some (fpropName, _, f) ← getFProp? e
      | return none

    let candidates ←
      -- if function head is a constant we look up global theorem
      -- otherwise we use hypothesis from local context
      match (← getFunHeadConst? f) with
        | .some funName => 
          pure <| (← FProp.getFPropRules funName fpropName).append (← getLocalRules fpropName)
        | none => getLocalRules fpropName

    if candidates.size = 0 then
      trace[Meta.Tactic.fprop.apply] "no suitable theorems found for {← ppExpr e}"

    for thm in candidates do
      trace[Meta.Tactic.fprop.unify] "trying to apply {← ppOrigin thm.origin} to {← ppExpr e}"
      if let some proof ← tryTheorem? e thm discharge? then
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

