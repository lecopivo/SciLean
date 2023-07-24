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

          let goals ←
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


/-- Takes lambda function `fun x => b` and splits it into composition of two functions. 

  Example:
    fun x => f (g x)      ==>   f ∘ g 
    fun x => f x + c      ==>   (fun y => y + c) ∘ f
    fun x => f x + g x    ==>   (fun (y₁,y₂) => y₁ + y₂) ∘ (fun x => (f x, g x))
 -/
def splitLambdaToComp (e : Expr) : MetaM (Expr × Expr) := do
  match e with 
  | .lam name type b bi => 
    withLocalDecl name bi type fun x => do
      let b := b.instantiate1 x
      let xId := x.fvarId!

      let ys := b.getAppArgs
      let mut f := b.getAppFn

      let mut lctx ← getLCtx
      let instances ← getLocalInstances

      let mut ys' : Array Expr := #[]
      let mut zs  : Array Expr := #[]

      for y in ys, i in [0:ys.size] do
        if y.containsFVar xId then
          let zId ← withLCtx lctx instances mkFreshFVarId
          lctx := lctx.mkLocalDecl zId (name.appendAfter (toString i)) (← inferType y)
          let z := Expr.fvar zId
          zs  := zs.push z
          ys' := ys'.push y
          f := f.app z
        else
          f := f.app y

      let y' ← mkProdElem ys'
      let g  ← mkLambdaFVars #[.fvar xId] y'

      f ← withLCtx lctx instances (mkLambdaFVars zs f)
      f ← mkUncurryFun zs.size f

      return (f, g)
    
  | _ => throwError "Error in `splitLambdaToComp`, not a lambda function!"

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
      return proof
    else
      forallTelescope e fun xs b => do
        let .some proof ← main b
          | return none
        cache e (← mkLambdaFVars xs proof)


  partial def main (e : Expr) : FPropM (Option Expr) := do

    let .some (fpropName, ext, f) ← getFProp? e
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
      match (body.hasLooseBVar 0), (body.hasLooseBVar 1) with
      | true, true =>
        trace[Meta.Tactic.fprop.step] "case let\n{← ppExpr e}"
        let f := Expr.lam xName xType (.lam yName yType body xBi) default
        let g := Expr.lam xName xType yValue default
        ext.lambdaLetRule e f g

      | true, false => 
        trace[Meta.Tactic.fprop.step] "case comp\n{← ppExpr e}"
        let f := Expr.lam yName yType body xBi
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
      else
        trace[Meta.Tactic.fprop.step] "case other\n{← ppExpr e}"
        applyTheorems e (ext.discharger)

    | _ => do
      trace[Meta.Tactic.fprop.step] "case other\n{← ppExpr e}"
      applyTheorems e (ext.discharger)

  partial def applyFVarApp (e : Expr) (discharge? : Expr → FPropM (Option Expr)) : FPropM (Option Expr) := do
    let .some (fpropName, ext, F) ← getFProp? e
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
    let .some (fpropName, ext, f) ← getFProp? e
      | return none

    let candidates ←
      -- if function head is a constant we look up global theorem
      -- otherwise we use hypothesis from local context
      match (← getFunHeadConst? f) with
        | .some funName => FProp.getFPropRules funName fpropName
        | none => getLocalRules fpropName

    if candidates.size = 0 then
      trace[Meta.Tactic.fprop.apply] "no suitable theorems found for {← ppExpr e}"

    for thm in candidates do
      trace[Meta.Tactic.fprop.unify] "trying to apply {← ppOrigin thm.origin} to {← ppExpr e}"
      if let some proof ← tryTheorem? e thm discharge? then
        return proof

    return none -- ext.lambdaLetRule e
    -- return none

  partial def synthesizeInstance (thmId : Origin) (x type : Expr) : MetaM Bool := do
    match (← trySynthInstance type) with
    | LOption.some val =>
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
      let type ← inferType val
      let (xs, bis, type) ← forallMetaTelescope type
      let type ← instantiateMVars type
      tryTheoremCore xs bis val type e thm discharge?
end

