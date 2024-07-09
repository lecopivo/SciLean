import SciLean.Tactic.FunTrans.Core
import SciLean.Lean.Meta.Basic
import SciLean.Util.RewriteBy

open Lean Meta Elab Term Command

namespace SciLean

initialize registerTraceClass `Meta.Tactic.fun_prop.generate

open Mathlib.Meta


structure DefineFunPropConfig where
  defineIfSimilarExists := true

/--
Given `statement` like `q(Continuous fun x : R => c * x)`, its proof `prf` and context like
`#[q(R), q((_: RealScalar R)), q(c)]`, create a new `fun_prop` theorem stating it.

You can prevent the theorem to be defined if already similar theorems exists by passing option
`cfg := { defineIfSimilarExists := false }`

TODO: We should iterate over transition theorems from the simplest to the most complicated.
 -/
def defineFunPropTheorem (statement proof : Expr) (ctx : Array Expr)
  (suffix : Option Name := none) (cfg : DefineFunPropConfig := {}) : MetaM Bool := do

  let .some (funPropDecl, f) ← Mathlib.Meta.FunProp.getFunProp? statement
    | throwError s!"unrecognized function proposition {← ppExpr statement}!"

  let .data fData ← FunProp.getFunctionData? f FunProp.defaultUnfoldPred {zeta:=false}
    | throwError s!"invalid function {← ppExpr f}"

  let .some funName ← fData.getFnConstName?
    | throwError s!"invalid function {← ppExpr f}"

  let argNames ← getConstArgNames funName true
  let argNames := fData.mainArgs.map (fun i => argNames[i]!)

  let similarTheorems ← FunProp.getDeclTheorems funPropDecl funName fData.mainArgs fData.args.size
  if similarTheorems.size ≠ 0 then
    unless cfg.defineIfSimilarExists do
      trace[Meta.Tactic.fun_prop.generate]
        "not generating `fun_prop` theorem for {statement} because similar theorems exist:
         {similarTheorems.map (fun t => t.thmOrigin.name)}"
      return false

  trace[Meta.Tactic.fun_prop.generate] "
     Generating `fun_prop` theorem for `{statement}`
     Function name:  {funName}
     Function trans: {funPropDecl.funPropName}
     Arguments:      {argNames}"

  if similarTheorems.size ≠ 0 then
    trace[Meta.Tactic.fun_prop.generate]
      "similar theorems already exists: {similarTheorems.map (fun t => t.thmOrigin.name)}"


  let declSuffix := argNames.foldl (init := "arg_") (fun s n => s ++ toString n)

  let mut thmName := funName.append (.mkSimple declSuffix)
      |>.append (.mkSimple funPropDecl.funPropName.lastComponentAsString)
      |>.appendAfter "_rule"
  if let .some s := suffix then
    thmName := thmName.appendAfter (toString s)

  let thmType ← mkForallFVars ctx statement >>= instantiateMVars
  let thmVal  ← mkLambdaFVars ctx proof >>= instantiateMVars

  if thmType.hasLevelParam then
    throwError "theorem statement {← ppExpr thmType} has level parameters!"
  if thmVal.hasLevelParam then
    throwError "theorem proof {← ppExpr thmVal} has level parameters!"

  let thmDecl : TheoremVal :=
  {
    name  := thmName
    type  := thmType
    value := thmVal
    levelParams := []
  }

  addDecl (.thmDecl thmDecl)
  FunProp.addTheorem thmName

  return true


partial def _root_.Mathlib.Meta.FunProp.RefinedDiscrTree.Trie.forValuesM {α} {m} [Monad m]
    (t : Mathlib.Meta.FunProp.RefinedDiscrTree.Trie α) (f : α → m Unit) : m Unit := do

  match t with
  | .node children =>
    for c in children do
      c.2.forValuesM f
  | .path _ child => child.forValuesM f
  | .values vs =>
    for v in vs do
      f v

partial def _root_.Mathlib.Meta.FunProp.RefinedDiscrTree.forValuesM {α} {m} [Monad m]
    (t : Mathlib.Meta.FunProp.RefinedDiscrTree α) (f : α → m Unit) : m Unit := do
  t.root.forM (fun _ trie => trie.forValuesM f)


/--
Given a proof of function property `proof` like `q(by fun_prop : Differentiable Real.sin)`
generate theorems for all the function properties that follow from this. -/
partial def defineTransitiveFunProp (proof : Expr) (ctx : Array Expr)
    (suffix : Option Name := none) : MetaM Unit := do
  trace[Meta.Tactic.fun_prop.generate] "generating transitive properties for `{← inferType proof}`"
  let s := FunProp.transitionTheoremsExt.getState (← getEnv)

  s.theorems.forValuesM fun thm => do
    trace[Meta.Tactic.fun_prop.generate] "trying transition theorem {thm.thmName}"
    let thmProof ← mkConstWithFreshMVarLevels thm.thmName
    let thmType ← inferType thmProof
    let (xs,_,thmType) ← forallMetaTelescope thmType
    let thmProof := mkAppN thmProof xs

    for x in xs do

      if (← isDefEq x proof) then
        let thmProof ← instantiateMVars thmProof
        let thmType ← instantiateMVars thmType

        -- filer out assigned mvars
        let xs' ← xs.filterM (m:=MetaM) (fun x => do pure (← instantiateMVars x).hasMVar)

        -- turn mvars to fvars
        let thmProof ← mkLambdaFVars xs' thmProof
        let thmType ← mkForallFVars xs' thmType
        forallTelescope thmType fun xs'' thmType => do

          let r ← defineFunPropTheorem thmType (thmProof.beta xs'') (ctx++xs'')
                     suffix {defineIfSimilarExists := false}

          -- if theorem has been successfully defined we generate all its transitive fun_prop theoresm
          if r then
            try
              defineTransitiveFunProp thmProof (ctx++xs') suffix
            catch err =>
              trace[Meta.Tactic.fun_prop.generate]
                s!"failed to generate transitive fun_prop theorems for {thm.thmName}
                   {← err.toMessageData.toString}"



open Mathlib.Meta
/-- Command `def_fun_prop (c : ℝ) : Continuous (fun x => foo c x) by unfold foo; fun_prop`
will define a new `fun_prop` theorem for function `foo` about continuity in `x`.
-/
elab  "def_fun_prop" doTrans:("with_transitive")? suffix:(ident)? bs:bracketedBinder* ":" e:term "by" t:tacticSeq  : command => do

  runTermElabM fun ctx₁ => do
    elabBinders bs fun ctx₂ => do
    let statement ← elabTermAndSynthesize (← `($e)) none
    let suffix := suffix.map (fun s => s.getId)

    let prf ← mkFreshExprMVar statement
    let (subgoals,_) ← Elab.runTactic prf.mvarId! t

    -- filter context variables whether they are used or not
    let ctx₁ := ctx₁.filter (fun x => statement.containsFVar x.fvarId! ||
                                      prf.containsFVar x.fvarId!)

    if subgoals.length ≠ 0 then
      throwError s!"failed to show {← ppExpr statement}"

    let ctx := (ctx₁++ctx₂)
    let _ ← defineFunPropTheorem statement prf ctx suffix
    if doTrans.isSome then
      defineTransitiveFunProp prf ctx suffix
