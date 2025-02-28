/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

This is modified version of Lean.Meta.Tactic.Simp.Main

-/
import Lean.Meta.Transform
import Lean.Meta.Tactic.Replace
import Lean.Meta.Tactic.UnifyEq
import Lean.Meta.Tactic.Simp.Rewrite
import Lean.Meta.Match.Value

import SciLean.Tactic.LSimp.Types
import SciLean.Util.HoldLet

open Lean Meta

namespace SciLean.Tactic.LSimp

initialize registerTraceClass `Meta.Tactic.simp.proj
initialize registerTraceClass `Meta.Tactic.simp.steps
initialize registerTraceClass `Meta.Tactic.simp.time
initialize registerTraceClass `Meta.Tactic.simp.cache


theorem pull_if_from_app {α β} (c : Prop) [Decidable c] (t e : α) (f : α → β) :
    f (if c then t else e) = if c then f t else f e := by
  if h : c then simp[h] else simp[h]

/-- Decide if `v` should kept as a let binding or should be reduced.

This is refined version of `zeta` option in vanila simp. It allows you decide if let binding should
be kept or reduced based on the value of the let binding.

For example `fun x => let y := x; y` should be reduced to `fun x => x` and the let binding
`let y := x` is completely pointless.

-/
def keepAsLetValue (v : Expr) : LSimpM Bool := do
  let v ← instantiateMVars v
  let v := v.consumeMData
  if v.isAppOfArity ``holdLet 2 then
    return true
  else if v.isAppOfArity ``Prod.mk 4 then
    return false
  else if v.isAppOfArity ``OfNat.ofNat 3 then
    return false
  else if v.isAppOfArity ``OfScientific.ofScientific 5 then
    return false
  -- else if v.isAppOfArity ``ite 5 then
  --   return false
  else if v.isFVar then
    return false
  -- else if v.isLambda then
  --   return false
  else if (← inferType v).isForall then
    return false
  else if ← isProof v then
    return false
  return true

partial def maybeLetBind (e : Expr) (name := `x) : LSimpM Result :=  do
  if e.isAppOfArity ``Prod.mk 4 then
    let r₁ ← maybeLetBind e.appFn!.appArg! name
    let r₂ ← maybeLetBind e.appArg! name
    if r₁.proof?.isSome || r₁.proof?.isSome then
      throwError "internal bug, function `maybeLetBind` can't handle proofs right now!"
    return { expr := ← mkAppM ``Prod.mk #[r₁.expr, r₂.expr], vars := r₁.vars ++ r₂.vars }
  else if ← keepAsLetValue e then

    -- todo: add option to enable this
    -- attempt at reusing existing variables but it does not work see
    -- for example see test/lsimp_fvar_reuse_issue.lean
    -- in that example is seems that `ldsimp` introduces the `a` fvar into the context
    -- let lctx ← getLCtx
    -- let E ← inferType e
    -- if let .some var ← lctx.findDeclM? (fun decl =>
    --                        if decl.hasValue &&
    --                           decl.value == e &&
    --                           decl.type == E then
    --                        return some decl.toExpr else return none) then
    --   return { expr := var }
    -- else
    let var ← introLetDecl name none e
    return { expr := var, vars := #[var] }
  else
    return { expr := e }


/-- Introduce a new let binding if `r.expr` is complicated enough i.e. `keepAsLetValue r.expr` is true.
```
  { expr := v, vars := xs }.maybeLetBind
  =
  { expr := x, vars := xs.push x}
```
where `x := v` is the new local declaration.

Structure constructors might get split into multiple let bindings.
```
  { expr := (u,v) }.maybeLetBind
  =
  { expr := (x,y), vars := #[x,y] }
```
where `x := u` and `y := v` are new local declarations. The variable `x` gets introduces if `u`
passes `keepAsLetValue` and similarly for `y` and `v`.

NOTE: currently only `Prod` gets split into multiple let bindings. -/
def Result.maybeLetBind (r : Result) (name := `x) : LSimpM Result :=timeThis "let binding" do
  let r' ← LSimp.maybeLetBind r.expr name
  return ← r.mkEqTrans r'


private def projectCore? (e : Expr) (i : Nat) : MetaM (Option Expr) := do
  let e := e.toCtorIfLit
  matchConstCtor e.getAppFn (fun _ => pure none) fun ctorVal _ =>
    let numArgs := e.getAppNumArgs
    let idx := ctorVal.numParams + i
    if idx < numArgs then
      return some (e.getArg! idx)
    else
      return none

partial def whnf' (e : Expr) : MetaM Expr :=
  withIncRecDepth <| whnfEasyCases e fun e => do
    let e' ← whnfCore e
    match (← reduceNat? e') with
    | some v => return v
    | none   =>
      match (← reduceNative? e') with
      | some v => return v
      | none   => return e'


def project? (e : Expr) (i : Nat) : MetaM (Option Expr) := do
  projectCore? (← whnf e) i
  -- projectCore? (← whnf e) i

/-- Reduce kernel projection `Expr.proj ..` expression. -/
def reduceProj? (e : Expr) : MetaM (Option Expr) := do
  match e with
  | .proj _ i c => project? c i -- config
  | _           => return none

def withSimpConfig (a : MetaM α) : SimpM α := do
  let cfg' ← Simp.getConfig
  withConfig (fun cfg =>
    {cfg with
     iota := cfg'.iota
     beta := cfg'.beta
     proj := if cfg'.proj then .yes else .no
     zeta := cfg'.zeta
     zetaDelta := cfg'.zetaDelta}) a


private def reduceProjFnAux? (e : Expr) : LSimpM (Option Expr) := do
  matchConst e.getAppFn (fun _ => pure none) fun cinfo _ => do
    match (← getProjectionFnInfo? cinfo.name) with
    | none => return none
    | some projInfo =>
      /- Helper function for applying `reduceProj?` to the result of `unfoldDefinition?` -/
      let reduceProjCont? (e? : Option Expr) : SimpM (Option Expr) := do
        match e? with
        | none   => pure none
        | some e =>
          match (← withSimpConfig (reduceProj? e.getAppFn)) with
          | some f => return some (mkAppN f e.getAppArgs)
          | none   => return none
      if projInfo.fromClass then
        -- `class` projection
        if (← getContext).isDeclToUnfold cinfo.name then
          /-
          If user requested `class` projection to be unfolded, we set transparency mode to `.instances`,
          and invoke `unfoldDefinition?`.
          Recall that `unfoldDefinition?` has support for unfolding this kind of projection when transparency mode is `.instances`.
          -/
          let e? ← withReducibleAndInstances <| unfoldDefinition? e
          if e?.isSome then
            Simp.recordSimpTheorem (.decl cinfo.name)
          trace[Meta.Tactic.simp.proj] "definition to unfold"
          return e?
        else
          /-
          Recall that class projections are **not** marked with `[reducible]` because we want them to be
          in "reducible canonical form". However, if we have a class projection of the form `Class.projFn (Class.mk ...)`,
          we want to reduce it. See issue #1869 for an example where this is important.
          -/
          unless e.getAppNumArgs > projInfo.numParams do
            return none
          let major := e.getArg! projInfo.numParams
          unless (← isConstructorApp major) do
            return none
          trace[Meta.Tactic.simp.proj] "unfold definition"
          reduceProjCont? (← withDefault <| unfoldDefinition? e)
      else
        -- `structure` projections
        trace[Meta.Tactic.simp.proj] "structure projection"
        reduceProjCont? (← unfoldDefinition? e)


private def reduceProjFn? (e : Expr) : LSimpM (Option Expr) := timeThis "proj" do
  match (← reduceProjFnAux? e) with
  | none => return none
  | some e' =>
    trace[Meta.Tactic.simp.proj] "{e} ==> {e'}"
    return e'


private def reduceFVar (cfg : Simp.Config) (thms : SimpTheoremsArray) (e : Expr) : LSimpM Expr := do
  let localDecl ← getFVarLocalDecl e
  if cfg.zetaDelta || thms.isLetDeclToUnfold e.fvarId! || localDecl.isImplementationDetail then
    if !cfg.zetaDelta && thms.isLetDeclToUnfold e.fvarId! then
      Simp.recordSimpTheorem (.fvar localDecl.fvarId)
    let some v := localDecl.value? | return e
    return v
  else
    return e


private partial def isMatchDef (declName : Name) : CoreM Bool := do
  let .defnInfo info ← getConstInfo declName | return false
  return go (← getEnv) info.value
where
  go (env : Environment) (e : Expr) : Bool :=
    if e.isLambda then
      go env e.bindingBody!
    else
      let f := e.getAppFn
      f.isConst && isMatcherCore env f.constName!

/--
Try to unfold `e`.
-/
private def unfold? (e : Expr) : LSimpM (Option Expr) := do
  let f := e.getAppFn
  if !f.isConst then
    return none
  let fName := f.constName!
  let ctx ← getContext
  let rec unfoldDeclToUnfold? : LSimpM (Option Expr) := do
    let options ← getOptions
    let cfg ← getConfig
    -- Support for issue #2042
    if cfg.unfoldPartialApp -- If we are unfolding partial applications, ignore issue #2042
       -- When smart unfolding is enabled, and `f` supports it, we don't need to worry about issue #2042
       || (smartUnfolding.get options && (← getEnv).contains (mkSmartUnfoldingNameFor fName)) then
      withDefault <| unfoldDefinition? e
    else
      -- `We are not unfolding partial applications, and `fName` does not have smart unfolding support.
      -- Thus, we must check whether the arity of the function >= number of arguments.
      let some cinfo := (← getEnv).find? fName | return none
      let some value := cinfo.value? | return none
      let arity := value.getNumHeadLambdas
      -- Partially applied function, return `none`. See issue #2042
      if arity > e.getAppNumArgs then return none
      withDefault <| unfoldDefinition? e
  if (← isProjectionFn fName) then
    return none -- should be reduced by `reduceProjFn?`
  else if ctx.config.autoUnfold then
    if ctx.simpTheorems.isErased (.decl fName) then
      return none
    else if hasSmartUnfoldingDecl (← getEnv) fName then
      withDefault <| unfoldDefinition? e
    else if (← isMatchDef fName) then
      let some value ← withDefault <| unfoldDefinition? e | return none
      let .reduced value ← reduceMatcher? value | return none
      return some value
    else
      return none
  else if ctx.isDeclToUnfold fName then
    unfoldDeclToUnfold?
  else
    return none


def withNewLemmas {α} (xs : Array Expr) (f : LSimpM α) : LSimpM α := do
  if (← getConfig).contextual then
    let mut s ← Simp.getSimpTheorems
    let mut updated := false
    for x in xs do
      if (← isProof x) then
        s ← s.addTheorem (.fvar x.fvarId!) x
        updated := true
    if updated then
      withSimpTheorems s f
    else
      f
  else
    f



partial def reduceStep (e : Expr) : LSimpM Expr := do
  let cfg ← getConfig
  let f := e.getAppFn
  if f.isMVar then
    return (← instantiateMVars e)
  if cfg.beta then
    if f.isHeadBetaTargetFn false then
      return f.betaRev e.getAppRevArgs
  -- TODO: eta reduction
  if cfg.proj then
    match (← reduceProjFn? e) with
    | some e => return e
    | none   => pure ()
  if cfg.iota then
    match (← reduceRecMatcher? e) with
    | some e => return e
    | none   => pure ()
  if cfg.zeta then
    if let some (args, _, _, v, b) := e.letFunAppArgs? then
      return mkAppN (b.instantiate1 v) args
    if e.isLet then
      return e.letBody!.instantiate1 e.letValue!
  match (← unfold? e) with
  | some e' =>
    trace[Meta.Tactic.simp.rewrite] "unfold {mkConst e.getAppFn.constName!}, {e} ==> {e'}"
    Simp.recordSimpTheorem (.decl e.getAppFn.constName!)
    return e'
  | none => return e


partial def reduce (e : Expr) : LSimpM Expr :=  /- withIncRecDepth -/  do
  let e' ← reduceStep e
  if e' == e then
    return e'
  else
    reduce e'


partial def simpProj (e : Expr) : LSimpM Result := do
  match (← Meta.reduceProj? e) with
  | some e =>
    return { expr := e }
  | none =>
    let s := e.projExpr!
    let motive? ← withLocalDeclD `s (← inferType s) fun s => do
      let p := e.updateProj! s
      if (← dependsOn (← inferType p) s.fvarId!) then
        return none
      else
        let motive ← mkLambdaFVars #[s] (← mkEq e p)
        if !(← isTypeCorrect motive) then
          return none
        else
          return some motive
    if let some motive := motive? then
      let r ← lsimp s
      let eNew := e.updateProj! r.expr
      match r.proof? with
      | none => return { expr := eNew, vars := r.vars }
      | some h =>
        let hNew ← mkEqNDRec motive (← mkEqRefl e) h
        return { expr := eNew, proof? := some hNew, vars := r.vars }
    else
      return { expr := (← ldsimp e) }

partial def simpConst (e : Expr) : LSimpM Result :=
  return { expr := (← reduce e) }

partial def lambdaTelescopeDSimp [Inhabited α] (e : Expr) (k : Array Expr → Expr → LSimpM α) : LSimpM α := do
  go #[] e
where
  go (xs : Array Expr) (e : Expr) : LSimpM α := do
    match e with
    | .lam n d b c => withLocalDecl n c (← ldsimp d) fun x => go (xs.push x) (b.instantiate1 x)
    | e => k xs e

partial def simpLambda (e : Expr) : LSimpM Result := do
  withParent e <| lambdaTelescopeDSimp e fun xs e => do
    withoutModifyingLCtx pure do withoutModifyingCache do withNewLemmas xs do
      let r ← lsimp e

      let (eNew,vars)  ← xs.foldrM (init:=(r.expr,r.vars)) fun x (e,vars) => do
        let deps ← collectForwardDeps #[x] false
        let (vars', vars) := vars.partition deps.contains
        let e ← mkLambdaFVars (#[x] ++ vars') e
        pure (e,vars)
      let eNew ← mkLambdaFVars vars eNew

      let r ← r.bindVars
      let pullLetOutOfLambda := false -- todo: turn this into `lsimp` config option
      let eNew ← if pullLetOutOfLambda then pure eNew else mkLambdaFVars xs r.expr
      match r.proof? with
      | none   => return { expr := eNew }
      | some h =>
        let p ← xs.foldrM (init := h) fun x h => do
          mkFunExt (← mkLambdaFVars #[x] h)
        return { expr := eNew, proof? := p }

      -- old implementation that does not pull let bindings out of lambda function
      -- let r ← lsimp e >>= (·.bindVars)
      -- let eNew ← mkLambdaFVars xs r.expr
      -- match r.proof? with
      -- | none   => return { expr := eNew }
      -- | some h =>
      --   let p ← xs.foldrM (init := h) fun x h => do
      --     mkFunExt (← mkLambdaFVars #[x] h)
      --   return { expr := eNew, proof? := p }


partial def simpArrow (e : Expr) : LSimpM Result := return { expr := e}
  -- trace[Debug.Meta.Tactic.simp] "arrow {e}"
  -- let p := e.bindingDomain!
  -- let q := e.bindingBody!
  -- let rp ← lsimp p
  -- trace[Debug.Meta.Tactic.simp] "arrow [{(← getConfig).contextual}] {p} [{← isProp p}] -> {q} [{← isProp q}]"
  -- if (← pure (← getConfig).contextual <&&> isProp p <&&> isProp q) then
  --   trace[Debug.Meta.Tactic.simp] "ctx arrow {rp.expr} -> {q}"
  --   withLocalDeclD e.bindingName! rp.expr fun h => do
  --     let s ← Simp.getSimpTheorems
  --     let s ← s.addTheorem (.fvar h.fvarId!) h
  --     withSimpTheorems s do
  --       let rq ← lsimp q
  --       match rq.proof? with
  --       | none    => mkImpCongr e rp rq
  --       | some hq =>
  --         let hq ← mkLambdaFVars #[h] hq
  --         /-
  --           We use the default reducibility setting at `mkImpDepCongrCtx` and `mkImpCongrCtx` because they use the theorems
  --           ```lean
  --           @implies_dep_congr_ctx : ∀ {p₁ p₂ q₁ : Prop}, p₁ = p₂ → ∀ {q₂ : p₂ → Prop}, (∀ (h : p₂), q₁ = q₂ h) → (p₁ → q₁) = ∀ (h : p₂), q₂ h
  --           @implies_congr_ctx : ∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p₁ → q₁) = (p₂ → q₂)
  --           ```
  --           And the proofs may be from `rfl` theorems which are now omitted. Moreover, we cannot establish that the two
  --           terms are definitionally equal using `withReducible`.
  --           TODO (better solution): provide the problematic implicit arguments explicitly. It is more efficient and avoids this
  --           problem.
  --           -/
  --         if rq.expr.containsFVar h.fvarId! then
  --           return { expr := (← mkForallFVars #[h] rq.expr), proof? := (← withDefault <| mkImpDepCongrCtx (← rp.getProof) hq) }
  --         else
  --           return { expr := e.updateForallE! rp.expr rq.expr, proof? := (← withDefault <| mkImpCongrCtx (← rp.getProof) hq) }
  -- else
  --   mkImpCongr e rp (← lsimp q)

partial def simpForall (e : Expr) : LSimpM Result := return { expr := e }
  -- withParent e do
  -- trace[Debug.Meta.Tactic.simp] "forall {e}"
  -- if e.isArrow then
  --   simpArrow e
  -- else if (← isProp e) then
  --   /- The forall is a proposition. -/
  --   let domain := e.bindingDomain!
  --   if (← isProp domain) then
  --     /-
  --     The domain of the forall is also a proposition, and we can use `forall_prop_domain_congr`
  --     IF we can simplify the domain.
  --     -/
  --     let rd ← simp domain
  --     if let some h₁ := rd.proof? then
  --       /- Using
  --       ```
  --       theorem forall_prop_domain_congr {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → Prop}
  --           (h₁ : p₁ = p₂)
  --           (h₂ : ∀ a : p₂, q₁ (h₁.substr a) = q₂ a)
  --           : (∀ a : p₁, q₁ a) = (∀ a : p₂, q₂ a)
  --       ```
  --       Remark: we should consider whether we want to add congruence lemma support for arbitrary `forall`-expressions.
  --       Then, the theroem above can be marked as `@[congr]` and the following code deleted.
  --       -/
  --       let p₁ := domain
  --       let p₂ := rd.expr
  --       let q₁ := mkLambda e.bindingName! e.bindingInfo! p₁ e.bindingBody!
  --       let result ← withLocalDecl e.bindingName! e.bindingInfo! p₂ fun a => withNewLemmas #[a] do
  --         let prop := mkSort levelZero
  --         let h₁_substr_a := mkApp6 (mkConst ``Eq.substr [levelOne]) prop (mkLambda `x .default prop (mkBVar 0)) p₂ p₁ h₁ a
  --         let q_h₁_substr_a := e.bindingBody!.instantiate1 h₁_substr_a
  --         let rb ← simp q_h₁_substr_a
  --         let h₂ ← mkLambdaFVars #[a] (← rb.getProof)
  --         let q₂ ← mkLambdaFVars #[a] rb.expr
  --         let result ← mkForallFVars #[a] rb.expr
  --         let proof := mkApp6 (mkConst ``forall_prop_domain_congr) p₁ p₂ q₁ q₂ h₁ h₂
  --         return { expr := result, proof? := proof }
  --       return result
  --   let domain ← dsimp domain
  --   withLocalDecl e.bindingName! e.bindingInfo! domain fun x => withNewLemmas #[x] do
  --     let b := e.bindingBody!.instantiate1 x
  --     let rb ← simp b
  --     let eNew ← mkForallFVars #[x] rb.expr
  --     match rb.proof? with
  --     | none   => return { expr := eNew }
  --     | some h => return { expr := eNew, proof? := (← mkForallCongr (← mkLambdaFVars #[x] h)) }
  -- else
  --   return { expr := (← dsimp e) }


@[inline] def _root_.Lean.Expr.app5? (e : Expr) (fName : Name) : Option (Expr × Expr × Expr × Expr × Expr) :=
  if e.isAppOfArity fName 5 then
    some (e.appFn!.appFn!.appFn!.appArg!.appArg!, e.appFn!.appFn!.appFn!.appArg!, e.appFn!.appFn!.appArg!, e.appFn!.appArg!, e.appArg!)
  else
    none



partial def simpLet (e : Expr) : LSimpM Result := do
  let .letE n t v b _ := e | unreachable!
  if (← getConfig).zeta then
    return { expr := b.instantiate1 v }
  else
    match (← Simp.getSimpLetCase n t b) with
    | .dep | .nondepDepVar =>
      let v' ← ldsimp v

      let (vVar,vars) ← do
        if ← keepAsLetValue v' then
          let var ← introLetDecl n t v'
          pure (var, #[var])
        else
          pure (v', #[])

      -- todo: add option to enable this
      -- -- special handling of `let x := if c then t else e`
      -- if let .some (_,c,_,t,e) := v'.app5? ``ite then
      --   let t := b.instantiate1 t
      --   let e := b.instantiate1 e
      --   let bx ← mkAppM ``ite #[c,t,e]
      --   let rbx ← lsimp bx
      --   return { rbx with vars := vars ++ rbx.vars }

      let bx := b.instantiate1 vVar
      let rbx ← lsimp bx
      return { rbx with vars := vars ++ rbx.vars }
    | .nondep =>
      let rv ← (lsimp v >>= (·.maybeLetBind n))

      let r : Result :=
        { expr := b.instantiate1 rv.expr
          proof? := ← rv.proof?.mapM (fun h => mkCongrArg (.lam n t b default) h)
          vars := rv.vars }

      -- -- special handling of `let x := if c then t else e`
      -- -- todo: move this to a specialized function
      -- if let .some (_,c,_,x,y) := rv.expr.app5? ``ite then
      --   let bx ← mkAppM ``ite #[c, .letE n t x b false, .letE n t y b false]
      --   let r' : Result :=
      --     { expr := bx
      --       proof? := ← mkAppM ``pull_if_from_app #[c, x, y, .lam n t b default]
      --       vars := rv.vars }

      --   let rbx ← lsimp bx
      --   return ← r.mkEqTrans r' >>= (fun r => r.mkEqTrans rbx)


      let bx := b.instantiate1 rv.expr
      let rbx ← lsimp bx
      return ← r.mkEqTrans rbx

partial def ldsimpImpl (e : Expr) : LSimpM Expr := timeThis "dsimp" do
  let cfg ← getConfig
  unless cfg.dsimp do
    return e
  let pre (e : Expr) : LSimpM TransformStep := do
    if let Simp.Step.visit r ← Simp.rewritePre (rflOnly := true) e then
      if r.expr != e then
        return .visit r.expr
    return .continue
  let post (e : Expr) : LSimpM TransformStep := do
    if let Simp.Step.visit r ← Simp.rewritePost (rflOnly := true) e then
      if r.expr != e then
        return .visit r.expr
    let mut eNew ← reduce e
    if eNew.isFVar then
      eNew ← reduceFVar cfg (← Simp.getSimpTheorems) eNew
    if eNew != e then return .visit eNew else return .done e
  transform (usedLetOnly := cfg.zeta) e (pre := pre) (post := post)

initialize ldsimpRef.set ldsimpImpl

partial def visitFn (e : Expr) : LSimpM Result := do
  let f := e.getAppFn
  let fNew ← lsimp f
  if fNew.expr == f then
    return { expr := e }
  else
    let args := e.getAppArgs
    let eNew := mkAppN fNew.expr args
    if fNew.proof?.isNone then return { expr := eNew, vars := fNew.vars }
    let mut proof ← fNew.getProof
    for arg in args do
      proof ← Meta.mkCongrFun proof arg
    return { expr := eNew, proof? := proof, vars := fNew.vars }

partial def congrArgs (r : Result) (args : Array Expr) : LSimpM Result := do
  if args.isEmpty then
    return r
  else
    let cfg ← getConfig
    let infos := (← getFunInfoNArgs r.expr args.size).paramInfo
    let mut r := r
    let mut i := 0
    for arg in args do
      if h : i < infos.size then
        trace[Debug.Meta.Tactic.simp] "app [{i}] {infos.size} {arg} hasFwdDeps: {infos[i].hasFwdDeps}"
        let info := infos[i]
        if cfg.ground && info.isInstImplicit then
          -- We don't visit instance implicit arguments when we are reducing ground terms.
          -- Motivation: many instance implicit arguments are ground, and it does not make sense
          -- to reduce them if the parent term is not ground.
          -- TODO: consider using it as the default behavior.
          -- We have considered it at https://github.com/leanprover/lean4/pull/3151
          r ← mkCongrFun r arg
        else if !info.hasFwdDeps then
          r ← mkCongr r (← lsimp arg)
        else if (← whnfD (← inferType r.expr)).isArrow then
          r ← mkCongr r (← lsimp arg)
        else
          r ← mkCongrFun r (← ldsimp arg)
      else if (← whnfD (← inferType r.expr)).isArrow then
        r ← mkCongr r (← lsimp arg)
      else
        r ← mkCongrFun r (← ldsimp arg)
      i := i + 1
    return r


partial def congrDefault (e : Expr) : LSimpM Result := do
  -- if let some result ← tryAutoCongrTheorem? e then
  --   result.mkEqTrans (← visitFn result.expr)
  -- else
    withParent e <| e.withApp fun f args => do
      congrArgs (← lsimp f) args

/-- Process the given congruence theorem hypothesis. Return true if it made "progress". -/
partial def processCongrHypothesis (h : Expr) : LSimpM Bool := do
  forallTelescopeReducing (← inferType h) fun xs hType => withoutModifyingCache do withNewLemmas xs do
    let lhs ← instantiateMVars hType.appFn!.appArg!
    let r ← withoutModifyingLCtx (·.bindVars) (lsimp lhs)
    let rhs := hType.appArg!
    rhs.withApp fun m zs => do
      let val ← mkLambdaFVars zs r.expr
      unless (← isDefEq m val) do
        Simp.throwCongrHypothesisFailed
      let mut proof ← r.getProof
      if hType.isAppOf ``Iff then
        try proof ← mkIffOfEq proof
        catch _ => Simp.throwCongrHypothesisFailed
      unless (← isDefEq h (← mkLambdaFVars xs proof)) do
        Simp.throwCongrHypothesisFailed
      /- We used to return `false` if `r.proof? = none` (i.e., an implicit `rfl` proof) because we
          assumed `dsimp` would also be able to simplify the term, but this is not true
          for non-trivial user-provided theorems.
          Example:
          ```
          @[congr] theorem image_congr {f g : α → β} {s : Set α} (h : ∀ a, mem a s → f a = g a) : image f s = image g s :=
          ...

          example {Γ: Set Nat}: (image (Nat.succ ∘ Nat.succ) Γ) = (image (fun a => a.succ.succ) Γ) := by
            simp only [Function.comp_apply]
          ```
          `Function.comp_apply` is a `rfl` theorem, but `dsimp` will not apply it because the composition
          is not fully applied. See comment at issue #1113

          Thus, we have an extra check now if `xs.size > 0`. TODO: refine this test.
      -/
      return r.proof?.isSome || (xs.size > 0 && lhs != r.expr)

/-- Try to rewrite `e` children using the given congruence theorem -/
partial def trySimpCongrTheorem? (c : SimpCongrTheorem) (e : Expr) : LSimpM (Option Result) :=
  -- Looks like that `withNewMCtxDepth` does not work well with `MetaLCtxM` so we need to
  -- add `withoutModifyingLCtx`
  withoutModifyingLCtx (fun r? => r?.mapM (Result.bindVars ·)) do
  withNewMCtxDepth do
  trace[Debug.Meta.Tactic.simp.congr] "{c.theoremName}, {e}"
  let thm ← mkConstWithFreshMVarLevels c.theoremName
  let (xs, bis, type) ← forallMetaTelescopeReducing (← inferType thm)
  if c.hypothesesPos.any (· ≥ xs.size) then
    return none
  let isIff := type.isAppOf ``Iff
  let lhs := type.appFn!.appArg!
  let rhs := type.appArg!
  let numArgs := lhs.getAppNumArgs
  let mut e := e
  let mut extraArgs := #[]
  if e.getAppNumArgs > numArgs then
    let args := e.getAppArgs
    e := mkAppN e.getAppFn args[:numArgs]
    extraArgs := args[numArgs:].toArray
  if (← isDefEq lhs e) then
    let mut modified := false
    for i in c.hypothesesPos do
      let x := xs[i]!
      try
        if (← processCongrHypothesis x) then
          modified := true
      catch _ =>
        trace[Meta.Tactic.simp.congr] "processCongrHypothesis {c.theoremName} failed {← inferType x}"
        -- Remark: we don't need to check ex.isMaxRecDepth anymore since `try .. catch ..`
        -- does not catch runtime exceptions by default.
        return none
    unless modified do
      trace[Meta.Tactic.simp.congr] "{c.theoremName} not modified"
      return none
    unless (← Simp.synthesizeArgs (.decl c.theoremName) bis xs) do
      trace[Meta.Tactic.simp.congr] "{c.theoremName} synthesizeArgs failed"
      return none
    let eNew ← instantiateMVars rhs
    let mut proof ← instantiateMVars (mkAppN thm xs)
    if isIff then
      try proof ← mkAppM ``propext #[proof]
      catch _ => return none
    if (← hasAssignableMVar proof <||> hasAssignableMVar eNew) then
      trace[Meta.Tactic.simp.congr] "{c.theoremName} has unassigned metavariables"
      return none
    congrArgs { expr := eNew, proof? := proof } extraArgs
  else
    return none

partial def congr (e : Expr) : LSimpM Result := do
  let f := e.getAppFn
  if f.isConst then
    let congrThms ← getSimpCongrTheorems
    let cs := congrThms.get f.constName!
    for c in cs do
      match (← trySimpCongrTheorem? c e) with
      | none   => pure ()
      | some r => return r
    congrDefault e
  else
    congrDefault e

partial def simpApp (e : Expr) : LSimpM Result := do
  if Simp.isOfNatNatLit e then
    -- Recall that we expand "orphan" kernel nat literals `n` into `ofNat n`
    return { expr := e }
  else
    congr e

partial def simpStep (e : Expr) : LSimpM Result := do
  match e with
  | .mdata m e   => let r ← lsimp e; return { r with expr := mkMData m r.expr }
  | .proj ..     => simpProj e
  | .app ..      => simpApp e
  | .lam ..      => simpLambda e
  | .forallE ..  => simpForall e
  | .letE ..     => simpLet e
  | .const ..    => simpConst e
  | .bvar ..     => unreachable!
  | .sort ..     => return { expr := e }
  | .lit ..      => return { expr := e }
  | .mvar ..     => return { expr := (← instantiateMVars e) }
  | .fvar ..     => return { expr := (← reduceFVar (← getConfig) (← Simp.getSimpTheorems) e) }


partial def cacheResult (e : Expr) (cfg : Simp.Config) (r : Result) : LSimpM Result := do
  if cfg.memoize && r.cache then
    let r ← r.bindVars
    trace[Meta.Tactic.simp.cache] "inserting: {e} ==> {r.expr}"
    cacheInsert e r
  return r


partial def simpLoop (e : Expr) : LSimpM Result := /- withIncRecDepth -/ do
  let cfg ← getConfig
  if (← get).numSteps > cfg.maxSteps then
    throwError "simp failed, maximum number of steps exceeded"
  else
    -- checkSystem "simp"
    modify fun s => { s with numSteps := s.numSteps + 1 }
    match (← pre e) with
    | .done r  => cacheResult e cfg r
    | .visit r => cacheResult e cfg (← r.mkEqTrans (← simpLoop r.expr))
    | .continue none => visitPreContinue cfg { expr := e }
    | .continue (some r) => visitPreContinue cfg r
where
  visitPreContinue (cfg : Simp.Config) (r : Result) : LSimpM Result := do
    let eNew ← reduceStep r.expr
    if eNew != r.expr then
      let r := { r with expr := eNew }
      cacheResult e cfg (← r.mkEqTrans (← simpLoop r.expr))
    else
      let r ← r.mkEqTrans (← simpStep r.expr)
      visitPost cfg r
  visitPost (cfg : Simp.Config) (r : Result) : LSimpM Result := do
    match (← post r.expr) with
    | .done r' => cacheResult e cfg (← r.mkEqTrans r')
    | .continue none => visitPostContinue cfg r
    | .visit r' | .continue (some r') => visitPostContinue cfg (← r.mkEqTrans r')
  visitPostContinue (cfg : Simp.Config) (r : Result) : LSimpM Result := do
    let mut r := r
    unless cfg.singlePass || e == r.expr do
      r ← r.mkEqTrans (← simpLoop r.expr)
    cacheResult e cfg r

partial def lsimpImpl (e : Expr) : LSimpM Result := do
--   withIncRecDepth do
  if (← isProof e) then
    return { expr := e }
  go
where
  go : LSimpM Result := do
    let cfg ← getConfig
    if cfg.memoize then
      -- try LSimp.Cache
      if let some result ← cacheFind? e then
        trace[Meta.Tactic.simp.cache] "reusing: {e} ==> {result.expr}"
        return result
      else
        trace[Meta.Tactic.simp.cache] "no cache for: {e}"
      -- try Sipm.Cache
      let cache := (← (← getThe State).simpState.get).cache
      if let some result := cache.find? e then
        trace[Meta.Tactic.simp.cache] "reusing from simp cache: {e} ==> {result.expr}"
        return { result with }

    trace[Meta.Tactic.simp.heads] "{repr e.toHeadIndex}"
    simpLoop e

initialize lsimpRef.set lsimpImpl


open private Lean.Meta.Simp.withSimpContext from Lean.Meta.Tactic.Simp.Main

/-- Run `lsimp` on `e` and process result with `k r' where `k` is executed in modified local context
where all `r.vars` are valid free vars.
 -/
def main (e : Expr) (k : Result → MetaM α)
    (ctx : Simp.Context)
    (stats : Simp.Stats := {})
    (methods : Simp.Methods := {}) : MetaM (α × Simp.Stats) := do

  -- try to instantiate as many mvars as possible
  -- this helps cache a lot as sometimes you can have universe mvars all over the place
  let e ← instantiateMVars e

  -- prepare state
  let lcacheRef : IO.Ref Cache ← IO.mkRef [{}] -- initialize cache stack to one!
  let stateRef : IO.Ref Simp.State ← IO.mkRef {stats with}
  let state : State := { cache := lcacheRef, simpState := stateRef }

  -- load context
  -- let ctx := { ctx with config := (← ctx.config.updateArith), lctxInitIndices := (← getLCtx).numIndices }
  Lean.Meta.Simp.withSimpContext ctx do

    -- run simp
    let (a,s) ← Meta.withoutModifyingLCtx (fun (r,s) => do pure (← k r,s)) do
      (lsimp e methods ctx state)

    -- trace cache - todo: use `traceCache function`
    (← s.cache.get).forM (fun c => do
      let l ← c.toList.mapM (fun (e,_) => do pure m!"{← ppExpr e}" )
      trace[Meta.Tactic.simp.cache] (l.foldl (init:="") (fun s e => s ++ "\n" ++ e))
      pure ())
    trace[Meta.Tactic.simp.cache] "cacher results "

    let simpState ← s.simpState.get
    return (a, {simpState with})


def lsimpMain (e : Expr) (k : Result → MetaM α)
    (ctx : Simp.Context) (simprocs : Simp.SimprocsArray := #[]) (discharge? : Option Simp.Discharge := none)
    (stats : Simp.Stats := {}) : MetaM (α × Simp.Stats) := do profileitM Exception "lsimp" (← getOptions) do
  match discharge? with
  | none   => main e k ctx stats (methods := Simp.mkDefaultMethodsCore simprocs)
  | some d => main e k ctx stats (methods := Simp.mkMethods simprocs d (wellBehavedDischarge := false))
