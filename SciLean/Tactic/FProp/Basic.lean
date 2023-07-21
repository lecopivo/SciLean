import SciLean.Tactic.FProp.Init

open Lean Meta Qq

namespace SciLean.FProp


def cache (e : Expr) (proof? : Option Expr) : FPropM (Option Expr) := -- return proof?
  match proof? with
  | .none => return none
  | .some proof => do
    modify (fun s => { s with cache := s.cache.insert e proof} )
    return proof


def getLocalRules (fpropName : Name) : MetaM (Array SimpTheorem) := do
  let mut arr : Array SimpTheorem := #[]

  let lctx ← getLCtx
  for var in lctx do
    let type := var.type
    
    if (type.getForallBody.getAppFn.constName? == .some fpropName) &&
       (var.kind ≠ Lean.LocalDeclKind.auxDecl) then
       -- dbg_trace "adding `{← ppExpr var.toExpr} : {←ppExpr type}` to local rules to be applied"
       -- dbg_trace "hasExprMVar {var.hasExprMVar}"
       -- dbg_trace "hasValue {var.hasValue}"
       -- dbg_trace "hasValue {repr var.kind}"
       arr := arr.push {
         proof := var.toExpr
         origin := .fvar var.fvarId
         rfl := false
       }

  return arr

-- returns proof of expression like given expression like `Differentiable K fun x => f x`
mutual 
  partial def fprop (e : Expr) : FPropM (Option Expr) := do

    if let .some proof := (← get).cache.find? e then
      trace[Meta.Tactic.fprop.step] "cached\n{e}"
      return proof
    else
      forallTelescope e fun xs b => do
        let .some proof ← main b
          | return none
        cache e (← mkLambdaFVars xs proof)


  partial def main (e : Expr) : FPropM (Option Expr) := do

    -- move all leading binders into the local context

    let .some (fpropName, ext, f) ← getFProp? e
      | -- not function property
        return none

    match f with
    | .letE .. => letTelescope f fun xs b => do 
      trace[Meta.Tactic.fprop.step] "case let x := ..; ..\n{← ppExpr e}"
      let e' := ext.replaceFTransFun e b
      fprop (← mkLambdaFVars xs e')
    | .lam _ _ (.bvar  0) _ => 
      trace[Meta.Tactic.fprop.step] "case id\n{← ppExpr e}"
      applyIdentityRule ext e
    | .lam _ _ (.letE ..) _ => 
      trace[Meta.Tactic.fprop.step] "case let\n{← ppExpr e}"
      applyLambdaLetRule ext e
    | .lam _ _ (.lam  ..) _ => 
      trace[Meta.Tactic.fprop.step] "case pi\n{← ppExpr e}"
      applyLambdaLambdaRule ext e
    | .lam _ _ b _ => do
      if !(b.hasLooseBVar 0) then
        trace[Meta.Tactic.fprop.step] "case const\n{← ppExpr e}"
        applyConstantRule ext e
      -- else if b.getAppFn.isFVar then
      --   trace[Meta.Tactic.fprop.step] "case fvar app\n{← ppExpr e}"
      --   return none
      else
        trace[Meta.Tactic.fprop.step] "case other\n{← ppExpr e}"
        applyTheorems e (ext.discharger)
    | _ => do
      trace[Meta.Tactic.fprop.step] "case other\n{← ppExpr e}"
      applyTheorems e (ext.discharger)
  where
    applyIdentityRule (ext : FPropExt) (e : Expr) : FPropM (Option Expr) := do
      ext.identityRule e

    applyConstantRule (ext : FPropExt) (e : Expr) : FPropM (Option Expr) := do
      ext.constantRule e

    applyLambdaLetRule (ext : FPropExt) (e : Expr) : FPropM (Option Expr) := do
      ext.lambdaLetRule e

    applyLambdaLambdaRule (ext : FPropExt) (e : Expr) : FPropM (Option Expr) := do
      ext.lambdaLambdaRule e

  partial def applyTheorems (e : Expr) (discharge? : Expr → FPropM (Option Expr)) : FPropM (Option Expr) := do
    let .some (fpropName, _, f) ← getFProp? e
      | return none

    let candidates ←
      -- if function head is a constant we look up global theorem
      -- otherwise we use hypothesis from local context
      match (← getFunHeadConst? f) with
        | .some funName => FProp.getFPropRules funName fpropName
        | none => getLocalRules fpropName

    for thm in candidates do
      if let some proof ← tryTheorem? e thm discharge? then
        return proof
    return none


  partial def synthesizeInstance (thmId : Origin) (x type : Expr) : MetaM Bool := do 
    match (← trySynthInstance type) with
    | LOption.some val =>
      if (← withReducibleAndInstances <| isDefEq x val) then
        return true
      else
        trace[Meta.Tactic.simp.discharge] "{← ppOrigin thmId}, failed to assign instance{indentExpr type}\nsythesized value{indentExpr val}\nis not definitionally equal to{indentExpr x}"
        return false
    | _ =>
      trace[Meta.Tactic.simp.discharge] "{← ppOrigin thmId}, failed to synthesize instance{indentExpr type}"
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
      let type ← inferType val
      let (xs, bis, type) ← forallMetaTelescope type
      let type ← instantiateMVars type
      tryTheoremCore xs bis val type e thm discharge?
end

