import Mathlib.Tactic.FunProp
import SciLean.Lean.Meta.Basic
import SciLean.Util.RewriteBy
import Mathlib.Lean.Meta.RefinedDiscrTree

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

  let .data fData ← withConfig (fun cfg => {cfg with zeta:=false}) <|
    FunProp.getFunctionData? f FunProp.defaultUnfoldPred
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

  let thmType ← (mkForallFVars ctx statement) >>= instantiateMVars
  let thmVal  ← (mkLambdaFVars ctx proof) >>= instantiateMVars

  -- replace level mvars with parameters
  let (thmVal,_) ← (Elab.Term.levelMVarToParam thmVal).run {}
  let lvlParams := (collectLevelParams {} thmVal).params

  -- assign lvl parameters in `tmmType`
  unless (← isDefEq thmType (← inferType thmVal)) do
    throwError "failed instantiating level parameters"
  let thmType ← instantiateMVars thmType

  let thmDecl : TheoremVal :=
  {
    name  := thmName
    type  := thmType
    value := thmVal
    levelParams := lvlParams.toList
  }

  addDecl (.thmDecl thmDecl)
  FunProp.addTheorem thmName

  return true


partial def _root_.Lean.Meta.RefinedDiscrTree.Trie.forValuesM {α} {m} [Monad m]
    (t : Lean.Meta.RefinedDiscrTree.Trie α) (f : α → m Unit) : m Unit := do

  match t with
  | .node children =>
    for c in children do
      c.2.forValuesM f
  | .path _ child => child.forValuesM f
  | .values vs =>
    for v in vs do
      f v

partial def _root_.Lean.Meta.RefinedDiscrTree.forValuesM {α} {m} [Monad m]
    (t : Lean.Meta.RefinedDiscrTree α) (f : α → m Unit) : m Unit := do
  t.root.forM (fun _ trie => trie.forValuesM f)


/--
Given a proof of function property `proof` like `q(by fun_prop : Differentiable Real.sin)`
generate theorems for all the function properties that follow from this. -/
partial def defineTransitiveFunProp (proof : Expr) (ctx : Array Expr)
    (suffix : Option Name := none) (recursive := false) : MetaM Unit := do
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
          if r && recursive then
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

    let statement ← instantiateMVars statement
    let prf ← instantiateMVars prf

    -- TODO: use built in rules for includeing/excluding variables!!!
    -- filter context variables whether they are used or not
    let ctx₁ := ctx₁.filter (fun x => statement.containsFVar x.fvarId! ||
                                      prf.containsFVar x.fvarId!)

    if subgoals.length ≠ 0 then
      throwError s!"failed to show {← ppExpr statement}"

    let ctx := (ctx₁++ctx₂)
    let _ ← defineFunPropTheorem statement prf ctx suffix
    if doTrans.isSome then
      defineTransitiveFunProp prf ctx suffix



namespace FunProp

syntax Parser.suffix := "add_suffix" ident
syntax Parser.trans := "with_transitive"
syntax Parser.argSubsets := "arg_subsets"
syntax Parser.config := Parser.suffix <|> Parser.trans <|> Parser.argSubsets

syntax Parser.funPropProof := "by" tacticSeq

open Lean

structure DefFunPropConfig where
  withTransitive := false
  suffix : Option Name := none
  argSubsets := false

open Lean Syntax Elab
def parseDefFunPropConfig (stx : TSyntaxArray ``Parser.config) : MetaM DefFunPropConfig := do

  let mut cfg : DefFunPropConfig := {}

  for s in stx do
    cfg ←
      match s.raw[0]! with
      | `(Parser.suffix| add_suffix $id:ident) =>
        if cfg.suffix.isSome then
          throwErrorAt s.raw s!"suffix already specified as `{cfg.suffix.get!}`"
        pure {cfg with suffix := id.getId}
      | `(Parser.trans| with_transitive) => pure {cfg with withTransitive := true}
      | `(Parser.argSubsets| arg_subsets) => pure {cfg with argSubsets := true}
      | _ => throwErrorAt s.raw "invalid option {s}"

  return cfg

def parseFunPropTactic (fId : Name) (stx : Option (TSyntax ``Parser.funPropProof)) : MetaM (TSyntax `tactic) := do
  match stx with
  | .some prf =>
      match prf.raw with
      | `(Parser.funPropProof| by $tac:tacticSeq) => pure ⟨tac.raw⟩
      | _ => Elab.throwUnsupportedSyntax
  | none =>
    let fIdent := mkIdent fId
    `(tactic| (unfold $fIdent; fun_prop))




open Lean Meta Elab Term in
def defFunProp (f : Ident) (args : TSyntaxArray `ident)
  (cfg : TSyntaxArray ``Parser.config) (bs : TSyntaxArray ``Parser.Term.bracketedBinder)
  (fprop : TSyntax `term) (proof : Option (TSyntax ``Parser.funPropProof)) : Command.CommandElabM Unit := do
  Elab.Command.liftTermElabM <| do
  -- resolve function name
  let fId ← ensureNonAmbiguous f (← resolveGlobalConst f)
  let info ← getConstInfo fId

  let cfg ← parseDefFunPropConfig cfg
  let tac ← parseFunPropTactic fId proof

  forallTelescope info.type fun xs _ => do
  Elab.Term.elabBinders bs.raw fun ctx₂ => do

    -- separate main arguments in which we want to define new function property
    let args := args.map (fun id => id.getId)
    let (mainArgs, otherArgs) ← xs.splitM (fun x => do
      let n ← x.fvarId!.getUserName
      return args.contains n)

    -- context variable of the statement and the proof
    let ctx := otherArgs ++ ctx₂

    -- check if all arguments are present
    for arg in args do
      if ← mainArgs.allM (fun a => do pure ((← a.fvarId!.getUserName) != arg)) then
        throwError s!"function `{fId}` does not have argument `{arg}`"

    -- uncurry function appropriatelly
    let lvls := info.levelParams.map (fun p => Level.param p)
    let g ← liftM <|
      mkLambdaFVars mainArgs (mkAppN (Expr.const info.name lvls) xs)
      >>=
      mkUncurryFun mainArgs.size

    -- create statement
    let fprop' ← Elab.Term.elabTerm fprop.raw (← mkArrow (← inferType g) (← mkFreshTypeMVar))
    let statement := (← mkAppM' fprop' #[g]).headBeta

    -- elaborate proof and check it worked
    let proof ← mkFreshExprMVar statement
    let (subgoals,_) ← liftM <| Elab.runTactic proof.mvarId! tac.raw
    if subgoals.length ≠ 0 then
       throwErrorAt fprop.raw s!"failed to prove `{← ppExpr statement}` with tactic `{tac.raw.prettyPrint}`"

    -- add new theorem to the enviroment
    let _ ← defineFunPropTheorem statement proof ctx cfg.suffix {}

    -- generate transitive theorem
    if cfg.withTransitive then
      defineTransitiveFunProp proof ctx cfg.suffix

    pure ()



/-- Define function property for a function in particular arguments.

Example:
```
def foo (x y z : ℝ) := x*x+y*z

def_fun_prop foo in x y z : Continuous
```
Proves continuity of `foo` in `x`, `y` and `z` as theorem `foo.arg_xyz.Continuous_rule`.

You can add additional assumptions, custom tactic to prove the property as demonstrated by the
following example:
```
def_fun_prop bar in x y
  add_suffix _simple
  with_transitive
  (xy : R×R) (h : xy.2 ≠ 0) : (DifferentiableAt R · xy) by unfold bar; fun_prop (disch:=assumption)
```
where
- `add_suffix _simple` adds `_simple` to the end of the generated theorems
- `with_transitive` also generates all theorems that can be infered from the current theorem.
  For example, `DifferentiableAt` implies `ContinuousAt`. All `fun_prop` transition theorems
  are tried to infer additional function properties.
- `(xy : R×R) (h : xy.2 ≠ 0)` are additional assumptions added to the theorem. These assumptions
  are stated in the context of the function so for example here we can use `R` without introducing it.
- `by unfold bar; fun_prop ...` you can specify custom tactic to prove the function property.
-/
elab "def_fun_prop " f:ident "in" args:ident* ppLine
     cfg:Parser.config*
     bs:bracketedBinder* " : " fprop:term proof:(Parser.funPropProof)? : command => do

  let c ← Lean.Elab.Command.liftTermElabM <| parseDefFunPropConfig cfg

  defFunProp f args cfg bs fprop proof

  -- generate the same with all argument subsets
  if c.argSubsets then
    for as in args.allSubsets do
      if as.size = 0 || as.size = args.size then
        continue
      defFunProp f as cfg bs fprop proof
