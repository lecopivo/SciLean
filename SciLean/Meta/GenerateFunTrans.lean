import SciLean.Lean.Array
import SciLean.Lean.Meta.Basic
import SciLean.Meta.GenerateFunProp
import SciLean.Tactic.Autodiff
import SciLean.Tactic.FunTrans.Core
import SciLean.Util.RewriteBy

open Lean Meta Elab Term Command Mathlib.Meta

namespace SciLean

initialize registerTraceClass `Meta.Tactic.fun_trans.generate

structure DefineFunTransConfig where
  defineIfSimilarExists := true
  defineNewFunction := true

def levelMVarToParamArray (es : Array Expr) : MetaM (Array Expr × Array Name) := do
  let e ← es.joinrM pure (fun x y => mkAppM ``PProd.mk #[x,y])
  let (e,_) ← (levelMVarToParam e).run {}
  let lvls := (collectLevelParams {} e).params

  let mut e := e
  let mut es := #[]
  while e.isAppOf ``PProd.mk do
    es := es.push e.appFn!.appArg!
    e := e.appArg!
  es := es.push e
  return (es,lvls)

open FunTrans
def generateFunTransDefAndTheorem (statement proof : Expr) (ctx : Array Expr)
    (suffix : Option Name := none) (cfg : DefineFunTransConfig := {}) :
    MetaM Bool := do

  let .some (_,lhs,rhs) := statement.eq?
    | throwError s!"equality expected, got {← ppExpr statement}"

  let .some (funTransDecl, f) ← Mathlib.Meta.FunTrans.getFunTrans? lhs
    | throwError s!"unrecognized function transformation {← ppExpr lhs}!"

  let .data fData ← withConfig (fun cfg => {cfg with zeta := false}) <|
    FunProp.getFunctionData? f FunProp.defaultUnfoldPred
    | throwError s!"invalid function {← ppExpr f}"

  let .some funName ← fData.getFnConstName?
    | throwError s!"invalid function {← ppExpr f}"

  let argNames ← getConstArgNames funName true
  let argNames := fData.mainArgs.map (fun i => argNames[i]!)

  let similarTheorems ←
      getTheoremsForFunction funName funTransDecl.funTransName fData.args.size fData.mainArgs
  if similarTheorems.size ≠ 0 then
    unless cfg.defineIfSimilarExists do
      trace[Meta.Tactic.fun_trans.generate]
        "not generating `fun_trans` theorem for {statement} because similar theorems exist:
         {similarTheorems.map (fun t => t.thmOrigin.name)}"
      return false


  trace[Meta.Tactic.fun_trans.generate] "
     Generating `fun_trans` theorem for `{statement}`
     Function name:  {funName}
     Function trans: {funTransDecl.funTransName}
     Arguments:      {argNames}"

  let declSuffix := argNames.foldl (init := "arg_") (fun s n => s ++ toString n)

  let defName := funName.append (.mkSimple declSuffix)
    |>.append (.mkSimple funTransDecl.funTransName.lastComponentAsString)
  let defName := if let .some s := suffix then defName.appendAfter (toString s) else defName
  let defCtx  := ctx.filter (fun x => rhs.containsFVar x.fvarId!)
  let defVal  ← mkLambdaFVars defCtx rhs >>= instantiateMVars

  -- turn level mvars to params
  let (defVal',lvls) ← levelMVarToParamArray #[defVal]
  let defVal := defVal'[0]!

  let decl : DefinitionVal :=
  {
    name  := defName
    type  := ← inferType defVal
    value := defVal
    hints := .regular 0
    safety := .safe
    levelParams := lvls.toList
  }

  if cfg.defineNewFunction then
    addDecl (.defnDecl decl)
    try
      compileDecl (.defnDecl decl)
    catch _ =>
      trace[Meta.Tactic.fun_trans.generate] "failed to complie {defName}!"

  let thmName := defName.appendAfter "_rule"
  let thmName := if let .some s := suffix then thmName.appendAfter (toString s) else thmName
  let thmCtx := ctx.filter (fun x => proof.containsFVar x.fvarId!)
  let thmType ←
    if cfg.defineNewFunction then
      mkForallFVars thmCtx (← mkEq lhs (← mkAppOptM defName (defCtx.map some)))
    else
      mkForallFVars thmCtx statement
    >>= instantiateMVars
  let thmVal  ← mkLambdaFVars thmCtx proof >>= instantiateMVars

  let thmDecl : TheoremVal :=
  {
    name  := thmName
    type  := ← instantiateMVars thmType
    value := ← instantiateMVars thmVal
    levelParams := lvls.toList
  }

  addDecl (.thmDecl thmDecl)
  FunTrans.addTheorem thmName

  return true


/--
Given a proof of function property `proof` like `q(by fun_prop : Differentiable Real.sin)`
generate theorems for all the function transformations that follow from this. -/
partial def defineTransitiveFunTransFromFunProp (proof : Expr) (ctx : Array Expr)
    (suffix : Option Name := none) : MetaM Unit := do
  trace[Meta.Tactic.fun_prop.generate] "generating transformations from `{← inferType proof}`"
  let s := FunTrans.fvarTheoremsExt.getState (← getEnv)

  s.theorems.forValuesM fun thm => do
    trace[Meta.Tactic.fun_prop.generate]
      "trying transition theorem {← ppOrigin (Origin.decl thm.thmName)}"
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

          let _ ← generateFunTransDefAndTheorem thmType (thmProof.beta xs'') (ctx++xs'')
                     suffix {defineIfSimilarExists := false, defineNewFunction := false }


open Mathlib.Meta
/-- Define function transformation, the command
-/
elab  "def_fun_trans" _doTrans:("with_transitive")? suffix:(ident)? bs:bracketedBinder* ":" e:term "by" c:Lean.Parser.Tactic.Conv.convSeq : command => do

  runTermElabM fun ctx₁ => do
    elabBinders bs fun ctx₂ => do
    let e ← elabTermAndSynthesize (← `($e)) none
    let e := e.headBeta.eta
    let (e',prf) ← elabConvRewrite e #[] (← `(conv| ($c)))
    let suffix := suffix.map (·.getId)
    let _ ← generateFunTransDefAndTheorem (← mkEq e e') prf (ctx₁++ctx₂) suffix


open Mathlib.Meta
elab  "abbrev_fun_trans" _doTrans:("with_transitive")? suffix:(ident)? bs:bracketedBinder* ":" e:term "by" c:Lean.Parser.Tactic.Conv.convSeq : command => do

  runTermElabM fun ctx₁ => do
    elabBinders bs fun ctx₂ => do
    let e ← elabTermAndSynthesize (← `($e)) none
    let e := e.headBeta.eta
    let (e',prf) ← elabConvRewrite e #[] (← `(conv| ($c)))
    let suffix := suffix.map (·.getId)
    let _ ← generateFunTransDefAndTheorem (← mkEq e e') prf (ctx₁++ctx₂) suffix { defineNewFunction := false }



namespace FunTrans

syntax Parser.suffix := "add_suffix" ident
syntax Parser.trans := "with_transitive"
syntax Parser.argSubsets := "arg_subsets"
syntax Parser.config := Parser.suffix <|> Parser.trans <|> Parser.argSubsets

syntax Parser.funTransProof := "by" Lean.Parser.Tactic.Conv.convSeq

open Lean

structure DefFunTransConfig where
  argSubsets := false
  suffix : Option Name := none

open Lean Syntax Elab
def parseDefFunTransConfig (stx : TSyntaxArray ``Parser.config) : MetaM DefFunTransConfig := do

  let mut cfg : DefFunTransConfig := {}

  for s in stx do
    cfg ←
      match s.raw[0]! with
      | `(Parser.suffix| add_suffix $id:ident) =>
        if cfg.suffix.isSome then
          throwErrorAt s.raw s!"suffix already specified as `{cfg.suffix.get!}`"
        pure {cfg with suffix := id.getId}
      | `(Parser.argSubsets| arg_subsets) => pure {cfg with argSubsets := true}
      | _ => throwErrorAt s.raw "invalid option {s}"

  return cfg

def parseFunTransConv (fId : Name) (stx : Option (TSyntax ``Parser.funTransProof)) : MetaM (TSyntax `conv) := do
  match stx with
  | .some prf =>
      match prf.raw with
      | `(Parser.funTransProof| by $tac:convSeq) => `(conv| ($tac))
      | _ => Elab.throwUnsupportedSyntax
  | none =>
    let fIdent := mkIdent fId
    `(conv| (unfold $fIdent; autodiff))

open Lean Meta Elab Term in

open Lean Meta Elab Term in
def defFunTrans (f : Ident) (args : TSyntaxArray `ident)
    (cfg : TSyntaxArray ``Parser.config) (bs : TSyntaxArray ``Parser.Term.bracketedBinder)
    (fprop : TSyntax `term) (proof : Option (TSyntax ``Parser.funTransProof)) (isDef := true) :
    Command.CommandElabM Unit := do

  Elab.Command.liftTermElabM <| do
  -- resolve function name
  let fId ← ensureNonAmbiguous f (← resolveGlobalConst f)
  let info ← getConstInfo fId

  let cfg ← parseDefFunTransConfig cfg
  let conv ← parseFunTransConv fId proof

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
    let lhs := (← mkAppM' fprop' #[g]).headBeta

    -- elaborate proof and check it worked
    let (rhs, proof) ← elabConvRewrite lhs #[] conv

    let statement ← mkEq lhs rhs

    -- add new theorem to the enviroment
    let _ ← generateFunTransDefAndTheorem statement proof ctx cfg.suffix {defineNewFunction:=isDef}

    pure ()


open Lean Meta Elab Term in
def defFunPropCommand (f : TSyntax `ident) (args : TSyntaxArray `ident)
    (cfg : TSyntaxArray `SciLean.FunTrans.Parser.config)
    (bs : TSyntaxArray `Lean.Parser.Term.bracketedBinder)
    (ftrans : TSyntax `term)
    (proof : Option (TSyntax `SciLean.FunTrans.Parser.funTransProof))
    (isDef := true) : CommandElabM Unit := do

  let c ← Lean.Elab.Command.liftTermElabM <| parseDefFunTransConfig cfg

  defFunTrans f args cfg bs ftrans proof isDef

  -- generate the same with all argument subsets
  if c.argSubsets then
    for as in args.allSubsets do
      if as.size = 0 || as.size = args.size then
        continue
      defFunTrans f as cfg bs ftrans proof isDef


/-- Define function transformation for a function in particular arguments.

Example:
```
def foo (x y z : ℝ) := x*x+y*z

def_fun_trans foo in x y z : fderiv ℝ
```
Computes derivative of `foo` in `x`, `y` and `z` and adds is as a new definition `foo.arg_xyz.fderiv`
and adds a new `fun_trans` theorem `foo.arg_xyz.fderiv_rule`.

You can add additional assumptions, custom tactic to prove the property as demonstrated by the
following example:
```
def_fun_prop bar in x y
  add_suffix _simple
  (xy : R×R) (h : xy.2 ≠ 0) : (DifferentiableAt R · xy) by unfold bar; fun_prop (disch:=assumption)
```
where
- `add_suffix _simple` adds `_simple` to the end of the generated theorems
- `(xy : R×R) (h : xy.2 ≠ 0)` are additional assumptions added to the theorem. These assumptions
  are stated in the context of the function so for example here we can use `R` without introducing it.
- `by unfold bar; autodiff ...` you can specify custom tactic to prove the function transformation.



Variant `abbrev_fun_trans`
---

Often the derivative/function transformation is simple enough that we do not want to hide it
behind a new definition like `foo.arg_xyz.fderiv_rule`. For example
`fderiv ℝ (fun x => matmul A x) x dx` should simplify to `matmul A dx` instead of
`matmul.arg_x.fderiv A x dx`. In cases like this, use `abbrev_fun_trans` which does not use
the newly defined function on the `fun_trans` theorem.

-/
elab (name:=defFunTransElab) "def_fun_trans " f:ident "in" args:ident* ppLine
     cfg:Parser.config*
     bs:bracketedBinder* " : " ftrans:term proof:(Parser.funTransProof)? : command => do
  defFunPropCommand f args cfg bs ftrans proof true

@[inherit_doc defFunTransElab]
elab "abbrev_fun_trans " f:ident "in" args:ident* ppLine
     cfg:Parser.config*
     bs:bracketedBinder* " : " ftrans:term proof:(Parser.funTransProof)? : command => do
  defFunPropCommand f args cfg bs ftrans proof false

end FunTrans
