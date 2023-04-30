import Std.Lean.Parser
import Mathlib.Tactic.NormNum.Core

import SciLean.Lean.Meta.Basic
import SciLean.Data.Prod
import SciLean.Core.Tactic.FunctionTransformation.Init

import SciLean.Core.Meta.FunctionProperty.Apply

open Lean Meta

namespace SciLean

namespace FunctionTransformation

def applyRule (transName : Name) (ruleType : FunTransRuleType) (args : Array Expr) : SimpM (Option Simp.Step) := do
  let .some rule ← findFunTransRule? transName ruleType
    | trace[Meta.Tactic.fun_trans.missing_rule] s!"Missing {ruleType} rule for `{transName}`."
      return none

  let proof ← mkAppNoTrailingM rule args
  let statement ← inferType proof
  let rhs := (← inferType proof).getArg! 2
  trace[Meta.Tactic.fun_trans.rewrite] s!"By basic rule `{rule}`\n{← ppExpr (statement.getArg! 1)}\n==>\n{← ppExpr rhs}"
  return .some (.visit (.mk rhs proof 0))


/-- Applies letBinop or letComp rule to `T (λ x => let y := ..; b)` as a simp step.
  
  - `x` has to be lambda free variable
  - `y` has to be let free variable
  - `b` is the body of the let binding
  -/
def applyLetRules (transName : Name) (x y b : Expr) : SimpM (Option Simp.Step) := do

  let xId := x.fvarId!
  let yId := y.fvarId!

  let .some gx ← yId.getValue?
    | return none

  -- if the let binding does not contain `x` then move the let binding out of the 
  -- function transformation
  if ¬(gx.containsFVar xId) then
    let e ← mkAppM transName #[← mkLambdaFVars #[y, x] b]
    return .some (.visit (.mk e none 0))

  let g ← mkLambdaFVars #[x] gx

  withLocalDecl (← yId.getUserName) default (← inferType y) λ y' => do
    let b := b.replaceFVarId yId y'

    if b.containsFVar xId then 
      let f ← mkLambdaFVars #[x,y'] b
      applyRule transName .letBinop #[f,g]
    else
      let f ← mkLambdaFVars #[y'] b
      applyRule transName .letComp #[f,g]

open Qq in
/-- Applies letBinop or letComp rule to `T (λ x y => b)` as a simp step.
  
  - `x` and `y` has to be lambda free variable
  - `b` is the body of the lambda function
  -/
def applyLambdaRules (transName : Name) (x y body : Expr) : SimpM (Option Simp.Step) := do

  -- Attempt applying `piMapComp` i.e. the case `λ g a => f a g (g (h a))`
  if let .forallE _ β X _ ← inferType x then
      -- rename variable to make the code more readable
      let α : Q(Type) ← inferType y
      let β : Q(Type) := β
      let X : Q(Type) := X
      -- let Y : Q(Type) ← inferType body
      let a : Q($α) := y
      let g : Q($β → $X) := x

      -- collect all subterms in the body of the form `g _`
      let (_,occurrences) ← StateT.run (s:=(#[] : Array Expr))
        (body.forEach' λ e => do
          if (e.getAppFn == g) && 
             (e.getAppNumArgs == 1) && 
             (e.containsFVar a.fvarId!) then
            modify λ s => s.push e
            return false
          return true)

      if 0 < occurrences.size then
        let occ := occurrences[0]!
        let ga ← mkAppM' g #[a]
        let h ← mkLambdaFVars #[a] (occ.getArg! 0)
        if ¬h.hasLooseBVars then
          let step ←
            withLocalDecl `gha default X λ gha =>
              let fbody := body.replace (λ e => if e == occ then gha else none)
              -- we have completely elimated `g` from the body, thus we can use `piMap` rule
              if (¬fbody.containsFVar g.fvarId!) &&
                 (occ == ga) then do
                let f ← mkLambdaFVars #[a, gha] fbody
                return ← applyRule transName .piMap #[f]
              else do
                let f ← mkLambdaFVars #[a, g, gha] fbody
                return ← applyRule transName .piMapComp #[f,h]

          return step

  -- TODO: Generalize this!
  -- Attempt applying `arrayMapComp` i.e. the case `∂† λ g a => f i g (g[h i])`
  if transName == `SciLean.adjointDifferential then
    let (_,occurrences) ← StateT.run (s:=(#[] : Array Expr))
      (body.forEach' λ e => do
        if (e.isAppOf ``getElem) &&
           (e.getAppNumArgs == 8) &&
           (e.getArg! 5 == x) &&
           (e.getArg! 6 |>.containsFVar y.fvarId!) then
          modify λ s => s.push e
          return false
        return true)

    if occurrences.size > 0 then
      let lhs ← mkAppM transName #[← mkLambdaFVars #[x,y] body]
      let occ := occurrences[0]!
      -- let ga ← mkAppOptM ``getElem #[none,none,none,none,none,x,y, none]
      let h ← mkLambdaFVars #[y] (occ.getArg! 6)
      if ¬h.hasLooseBVars then
        let step : Option Simp.Step ← 
          withLocalDecl `gha default (← inferType occ) λ gha => do
            let fbody := body.replace (λ e => if e == occ then gha else none)
            -- we have completely elimated `g` from the body, thus we can use `piMap` rule
            if (¬fbody.containsFVar x.fvarId!) &&
               (occ.getArg! 6 == y) then do
              let f ← mkLambdaFVars #[y, gha] fbody
              let proof ← mkAppNoTrailingM `SciLean.adjointDifferential.rule_piMap #[f]
              let statement ← inferType proof
              let rhs := statement.getArg! 2
              dbg_trace s!"Array comp motive: {← ppExpr f}"
              trace[Meta.Tactic.fun_trans.rewrite] s!"By rule arrayMap `\n{← ppExpr (statement.getArg! 1)}\n==>\n{← ppExpr rhs}"
              return .some (.visit (.mk rhs proof 0))
            else do
              let f ← mkLambdaFVars #[y, x, gha] fbody
              let proof ← mkAppNoTrailingM `SciLean.adjointDifferential.rule_piMapComp #[f,h]
              let statement ← inferType proof
              let rhs := statement.getArg! 2
              dbg_trace s!"Array comp motive f: {← ppExpr f}"
              dbg_trace s!"Array comp motive h: {← ppExpr h}"
              trace[Meta.Tactic.fun_trans.rewrite] s!"By rule arrayMapComp`\n{← ppExpr (statement.getArg! 1)}\n==>\n{← ppExpr rhs}"
              return .some (.visit (.mk rhs proof 0))
        return step

  let f ← mkLambdaFVars #[y,x] body
  applyRule transName .swap #[f]


/-- Apply rule for identity, constant or evaluation to `T (λ x => b)` as a simp step.

  - `x` has to be lambda free variable
  - `b` is the body of the lambda function
 
  Handling these cases: 
    1. identity: T (λ x => x)
    2. constant: T (λ y => x)
    3. evaluation: T (λ f => f x) 
-/
def applySimpleRules (transName : Name) (x b : Expr) : SimpM (Option Simp.Step) := do

  let xId := x.fvarId!

  -- identity - (λ x => x)
  if (b == x) then
    return ← (applyRule transName .id #[← xId.getType])

  -- constant - (λ y => x)
  if ¬(b.containsFVar xId) then
    return ← (applyRule transName .const #[← xId.getType, b])

  -- evaluation - (λ f => f x)
  if let .app f x' := b then
    if (f == x) && ¬(x'.containsFVar xId) then
      return ← (applyRule transName .eval #[(← inferType b), x'])

  return none


/-- Applies the composition rule to `T (λ x => b)` as a simp step

  - `x` has to be lambda free variable
  - `b` is the body of the lambda function - rule applies only if `b` is in the form `f (g x)`

  -/
def applyCompRules (transName : Name) (x b : Expr) : SimpM (Option Simp.Step) := do

  let xId := x.fvarId!

  if ¬b.isApp then 
    return none

  let F := b.getAppFn
  let args := b.getAppArgs

  -- Not sure how to handle this case, does it come up?
  if F.containsFVar xId then
    throwError s!"Composition case: the head of the expression {← ppExpr b} depends on the argument {← ppExpr x}. TODO: handle this case!"

  let .some constName := F.constName?
    | trace[Meta.Tactic.fun_trans.rewrite] s!"Can handle only applications of contants! Got `{← ppExpr b}` which is an application of `{← ppExpr F}`"
      return none

  let arity ← getConstArity constName
  if args.size = arity then
    let some (proof,thrm) ← applyCompTheorem transName constName args x
      | throwError s!"Failed at applying composition theorem for transformation `{transName}` and function `{constName}`"
    let statement ← inferType proof
    let rhs := statement.getArg! 2
    trace[Meta.Tactic.fun_trans.rewrite] s!"By composition theorem `{thrm}`\n{← ppExpr (statement.getArg! 1)}\n==>\n{← ppExpr rhs}"

    return .some (.visit (.mk rhs proof 0))
  else if args.size > arity then
    throwError s!"Constant {constName} has too many applied arguments in {← ppExpr b}. TODO: handle this case!"
  else
    throwError s!"Constant {constName} has too few applied arguments in {← ppExpr b}. TODO: handle this case!"

-- TODO: Move this somewhere else and add an environment extension for this to fetch this dynamically
def getFunTransStructureRule (transName structName : Name) : MetaM (Option Name) := do
  if (structName == ``Prod) then
    if (transName == `SciLean.adjointDifferential) then
      return `SciLean.adjointDifferential.structure_rule.Prod 
    if (transName == `SciLean.reverseDifferential) then
      return `SciLean.reverseDifferential.structure_rule.Prod 
  return none

/--
If `x` is an element of a structure type and there is a specialized transformation
rule for this structure apply this rule to `T λ x => b`.
-/
def tryStructureRule? (transName : Name) (x b : Expr) : SimpM (Option Simp.Step) := do

  let X ← whnf (← inferType x)

  let .const structName us := X.getAppFn
    | return none 

  let some info := getStructureInfo? (← getEnv) structName
    | return none
  
  let some rule ← getFunTransStructureRule transName info.structName
    | return none

  let projArgs := (X.getAppArgs.push x)
  let xprojs := info.fieldInfo.map λ fieldInfo => 
                  mkAppN (.const fieldInfo.projFn us) projArgs

  let xprojTypes ← xprojs.mapM λ xi => inferType xi

  let xName ← x.fvarId!.getUserName
  let xprojDecls := info.fieldInfo.mapIdx λ i fieldInfo => 
                      (xName.appendAfter (toString fieldInfo.fieldName), default, λ _ => pure xprojTypes[i]!)

  let step ← 
    withLocalDecls xprojDecls λ xps => do

      let replaceRules := xprojs.zip xps

      let b' := b.replace (λ e => do 
        for (val, fvar) in replaceRules do
          if e == val then
            return fvar
        none)

      -- no projection was found
      if xps.all λ xp => ¬(b'.containsFVar xp.fvarId!) then
        return none

      let f ← mkLambdaFVars (xps.reverse.push x) b'

      let proof ← mkAppNoTrailingM rule #[f]
      let statement ← inferType proof
      let rhs := statement.getArg! 2
      trace[Meta.Tactic.fun_trans.rewrite] s!"By structure rule {rule} `\n{← ppExpr (statement.getArg! 1)}\n==>\n{← ppExpr rhs}"
      return .some (.visit (.mk rhs proof 0))

  return step

/-- Transform `T f` according to the core transformation rules.
  -/
def main (transName : Name) (f : Expr) : SimpM (Option Simp.Step) := do

  trace[Meta.Tactic.fun_trans.step] s!"\n{← ppExpr f}"

  match f with
  | .lam .. => lambdaLetTelescope f λ xs b => do

    let x := xs[0]!

    if let some step ← tryStructureRule? transName x (← mkLambdaFVars xs[1:] b) then
      return step

    if xs.size > 1 then
      let y := xs[1]!

      let b ← mkLambdaFVars xs[2:] b
      
      if ← y.fvarId!.isLetVar then
        -- λ x => let y := ..; b
        applyLetRules transName x y b
      else
        -- λ x y => b
        applyLambdaRules transName x y b

    else 

      let b ← mkLambdaFVars xs[2:] b

      -- Change expression like `xy.1` back to `xy.
      let b ← revertStructureProj b

      -- λ x => x | λ y => x | λ f => f x
      if let .some r ← applySimpleRules transName x b then
        return r

      -- λ x => f (g x)
      if let .some r ← applyCompRules transName x b then
        return r


      return none

  | .letE .. => letTelescope f λ xs b => do
    -- swap all let bindings and the function transformation
    let f' ← mkLambdaFVars xs (← mkAppM transName #[b])
    return .some (.visit (.mk f' none 0))

  | _ => return none

/-- 
  Is expression `e` of the form `T f x₀ x₁ .. xₙ` where `T` is some function transformation?

  Return `(T, f, #[x₀,...,xₙ])`
 -/
def getFunctionTransform (e : Expr) : MetaM (Option (Name × Expr × Array Expr)) := do
  let T := e.getAppFn
  let args := e.getAppArgs
  if let .some (transName, _) := T.const? then

    let env ← getEnv
    if ¬(funTransDefAttr.hasTag env transName) then
      return none
    
    let info ← getConstInfo transName
    forallTelescope info.type λ xs _ => do
      -- find the id of the first explicit binder
      if let .some fId ← xs.findIdxM? (λ x => do pure (← x.fvarId!.getBinderInfo).isExplicit) then
        if args.size < fId then
          return none
        else
          return some (transName, args[fId]!, args[fId+1:])
      else
        return none
  else 
    return none

/--
Heuristic whether expression `e` is performing any meaningful computation. This 
is used when normalizing let bindings. Computationally meaningless let bindings are
removed.
-/
def _root_.Lean.Expr.doesComputation (e : Expr) : Bool := 
  match e with
  | .app f x => 
    x.isFVar || x.isBVar || f.isFVar || x.isBVar || doesComputation f || doesComputation x
  | _ => false

partial def normalizeLet? (e : Expr) : MetaM (Option Expr) := do
  let e' ← flattenLet e
  let (e', flag) := run e' (e' != e)
  if flag then pure (some e') else pure none
where 
  run (e : Expr) (didNormalize : Bool) : Expr × Bool :=
  match e with
  | .letE xName xType xVal body _ =>
    if body == .bvar 0 then
      (xVal, true)

    -- remove let binding if it is not doing any meaningful computation
    else if ¬xVal.doesComputation then
      run (body.instantiate1 xVal) true

    -- the let binding is not used at all
    else if ¬(body.hasLooseBVar 0) then
      run (body.instantiate1 xVal) true

    else
      let (body', didNormalize) := run body didNormalize
      (.letE xName xType xVal body' default, didNormalize)
  | _ => (e, didNormalize)


def tryFunTrans? (post := false) (e : Expr) : SimpM (Option Simp.Step) := do

  if post then 
    if let .some e' ← normalizeLet? e then
      trace[Meta.Tactic.fun_trans.normalize_let] s!"\n{← Meta.ppExpr e}\n==>\n{← Meta.ppExpr e'}"

      return .some (.visit (.mk e' none 0))
      
  
  if let .some (transName, f, args) ← getFunctionTransform e then
    if let .some step ← main transName f then


      let step := step.updateResult (← args.foldlM (init:=step.result) λ step' arg => Simp.mkCongrFun step' arg)

      return step

  return none


variable (ctx : Simp.Context) (useSimp := true) in
mutual
  /-- A discharger which calls `norm_num`. -/
  partial def discharge (e : Expr) : SimpM (Option Expr) := do (← deriveSimp e).ofTrue

  /-- A `Methods` implementation which calls `norm_num`. -/
  partial def methods : Simp.Methods :=
    if useSimp then {
      pre := fun e ↦ do
        Simp.andThen (← Simp.preDefault e discharge) tryFunTrans?
      post := fun e ↦ do
        Simp.andThen (← Simp.postDefault e discharge) (tryFunTrans? (post := true))
      discharge? := discharge
    } else {
      pre := fun e ↦ Simp.andThen (.visit { expr := e }) tryFunTrans?
      post := fun e ↦ Simp.andThen (.visit { expr := e }) (tryFunTrans? (post := true))
      discharge? := discharge
    }

  /-- Traverses the given expression using simp and normalises any numbers it finds. -/
  partial def deriveSimp (e : Expr) : MetaM Simp.Result :=
    (·.1) <$> Simp.main e ctx (methods := methods)
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
def funTransAt (g : MVarId) (ctx : Simp.Context) (fvarIdsToSimp : Array FVarId)
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

/-- Constructs a simp context from the simp argument syntax. -/
def getSimpContext (args : Syntax) (simpOnly := false) :
    TacticM Simp.Context := do
  let simpTheorems ←
    if simpOnly then simpOnlyBuiltins.foldlM (·.addConst ·) {} else getSimpTheorems
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
def elabFunTrans (args : Syntax) (loc : Syntax)
    (simpOnly := false) (useSimp := true) : TacticM Unit := do
  let ctx ← getSimpContext args (!useSimp || simpOnly)
  let ctx := {ctx with config := {ctx.config with iota := true, zeta := false, singlePass := true}}
  let g ← getMainGoal
  let res ← match expandOptLocation loc with
  | .targets hyps simplifyTarget => funTransAt g ctx (← getFVarIds hyps) simplifyTarget useSimp
  | .wildcard => funTransAt g ctx (← g.getNondepPropHyps) (simplifyTarget := true) useSimp
  match res with
  | none => replaceMainGoal []
  | some (_, g) => replaceMainGoal [g]


open Lean.Parser.Tactic in
elab (name := funTrans) "fun_trans" only:&" only"? args:(simpArgs ?) loc:(location ?) : tactic =>
  elabFunTrans args loc (simpOnly := only.isSome) (useSimp := true)


open Lean Elab Tactic Lean.Parser.Tactic

syntax (name := funTransConv) "fun_trans" &" only"? (simpArgs)? : conv

/-- Elaborator for `norm_num` conv tactic. -/
@[tactic funTransConv] def elabFunTransConv : Tactic := fun stx ↦ withMainContext do
  let ctx ← getSimpContext stx[2] !stx[1].isNone
  let ctx := {ctx with config := {ctx.config with iota := true, zeta := false, singlePass := true}}
  Conv.applySimpResult (← deriveSimp ctx (← instantiateMVars (← Conv.getLhs)) (useSimp := true))
