import SciLean.Tactic.DataSynth.Types
import SciLean.Tactic.DataSynth.Theorems
import Batteries.Tactic.Exact

import Lean.Meta.Transform

namespace SciLean.Tactic.DataSynth

open Lean Meta

/-- Tracing node that does not do any pretty printing so it is usefull for profiling. -/
private def withProfileTrace (msg : String) (x : DataSynthM α) : DataSynthM α :=
  withTraceNode `Meta.Tactic.data_synth.profile (fun _ => return msg) x

private def withMainTrace (msg : Except Exception α → DataSynthM MessageData) (x : DataSynthM α) :
    DataSynthM α :=
  withTraceNode `Meta.Tactic.data_synth msg x


def Simp.lsimp (e : Expr) : SimpM Simp.Result :=
  let r := do
    let r ← LSimp.lsimp e
    r.bindVars
  fun mthds ctx s => do
    let mthds := Simp.MethodsRef.toMethods mthds
    let cache : IO.Ref LSimp.Cache ← IO.mkRef {}
    let r := r mthds ctx {cache := cache, simpState := s}
    withoutModifyingLCtx
      (fun (r,_) => return { expr := r.expr, proof? := r.proof?})
      r


def reduceProdProj (e : Expr) : Expr :=
  match e with
  | .proj ``Prod 0 xy
  | mkApp3 (.const ``Prod.fst _) _ _ xy =>
    match reduceProdProj xy with
    | (mkApp4 (.const ``Prod.mk _) _ _ x _) => x
    | xy => .proj ``Prod 0 xy
  | .proj ``Prod 1 xy
  | mkApp3 (.const ``Prod.snd _) _ _ xy =>
    match reduceProdProj xy with
    | (mkApp4 (.const ``Prod.mk _) _ _ _ y) => y
    | xy => .proj ``Prod 1 xy
  | _ => e


def normalizeLet' (e : Expr) : CoreM Expr :=

 Lean.Core.transform e
   (post := fun e =>
     match e with
     | mkApp3 (.const ``Prod.fst _) _ _ (mkApp4 (.const ``Prod.mk _) _ _ x y) =>
       return .done x
     | mkApp3 (.const ``Prod.snd _) _ _ (mkApp4 (.const ``Prod.mk _) _ _ x y) =>
       return .done y
     | .proj ``Prod 0 (mkApp4 (.const ``Prod.mk _) _ _ x y) =>
       return .done x
     | .proj ``Prod 1 (mkApp4 (.const ``Prod.mk _) _ _ x y) =>
       return .done y
     | _ => return .done e)

   (pre := fun e =>
     match e with
     | .letE n t v b ndep =>
       match v with
       | .letE n' t' v' v ndep' =>
         let b := b.liftLooseBVars 1 1
         return .visit (.letE n' t' v' (.letE n t v b ndep) ndep')

       | (Expr.mkApp4 (.const ``Prod.mk [u,v]) X Y x y) =>

         let b := b.liftLooseBVars 1 2
         let b := b.instantiate1 (Expr.mkApp4 (.const ``Prod.mk [u,v]) X Y (.bvar 1) (.bvar 0))

         return .visit <|
           .letE (n.appendAfter "₁") X x (nonDep:=ndep) <|
           .letE (n.appendAfter "₂") Y (y.liftLooseBVars 0 1) (nonDep:=ndep) b

       | (.bvar ..) | (.fvar ..) | (.lam ..) =>
         return .visit <| b.instantiate1 v

       | (.app (.lam _ _ b' _) x) =>
         return .visit <| .letE n t (b'.instantiate1 x) b ndep
       | _ => return .continue
     | _ => return .continue)


open Lean Meta in
partial def splitLet (e : Expr) : Expr :=
  match e.headBeta with
  | .letE n t v b ndep =>

    match v.headBeta with
    | .letE n' t' v' v ndep' =>
      let b := b.liftLooseBVars 1 1
      splitLet <| .letE n' t' v' (.letE n t v b ndep) ndep'

    | (Expr.mkApp4 (.const ``Prod.mk [u,v]) X Y x y) =>

      let b := b.liftLooseBVars 1 2
      let b := b.instantiate1 (Expr.mkApp4 (.const ``Prod.mk [u,v]) X Y (.bvar 1) (.bvar 0))

      splitLet <|
        .letE (n.appendAfter "₁") X x (nonDep:=ndep) <|
        .letE (n.appendAfter "₂") Y (y.liftLooseBVars 0 1) (nonDep:=ndep) b

    | (.bvar ..) | (.fvar ..) | (.lam ..) =>
      splitLet <| b.instantiate1 v

    | (.app (.lam _ _ b' _) x) =>
      splitLet <| .letE n t (b'.instantiate1 x) b ndep

    | v =>
      let v' := splitLet v
      if v==v' then
        .letE n t v' (splitLet b) ndep
      else
        splitLet (.letE n t v' (splitLet b) ndep)

  | .proj ``Prod ..
  | (mkApp3 (.const ``Prod.fst _) ..)
  | (mkApp3 (.const ``Prod.snd _) ..) =>
    let v' := reduceProdProj e
    if v'==e then
      e
    else
      splitLet v'
  | .app f x =>
    .app (splitLet f) (splitLet x)
  | .lam n t b bi =>
    .lam n t (splitLet b) bi
  | .mdata d e =>
    .mdata d (splitLet e)
  | e => e


open Lean Meta in
partial def normalizeCore (e : Expr) : DataSynthM Expr := do
  checkCache { val := e : ExprStructEq } fun _ => Core.withIncRecDepth do
    match e.headBeta with
    | .letE n t v b ndep =>

      match v.headBeta with
      | .letE n' t' v' v ndep' =>
        let b := b.liftLooseBVars 1 1
        normalizeCore <| .letE n' t' v' (.letE n t v b ndep) ndep'

      | (Expr.mkApp4 (.const ``Prod.mk [u,v]) X Y x y) =>

        let b := b.liftLooseBVars 1 2
        let b := b.instantiate1 (Expr.mkApp4 (.const ``Prod.mk [u,v]) X Y (.bvar 1) (.bvar 0))

        normalizeCore <|
          .letE (n.appendAfter "₁") X x (nonDep:=ndep) <|
          .letE (n.appendAfter "₂") Y (y.liftLooseBVars 0 1) (nonDep:=ndep) b

      | (.bvar ..) | (.fvar ..) | (.lam ..) =>
        normalizeCore <| b.instantiate1 v

      | (.app (.lam _ _ b' _) x) =>
        normalizeCore <| .letE n t (b'.instantiate1 x) b ndep

      | v => do
        let v' ← normalizeCore v
        if v==v' then
          let b' ← normalizeCore b
          if ¬b'.hasLooseBVar 0 then
            return b'.lowerLooseBVars 1 1
          else
            return (.letE n t v' b' ndep)
        else
          normalizeCore (.letE n t v' b ndep)

    | .proj ``Prod 0 xy =>
      match (← normalizeCore xy) with
      | mkApp4 (.const ``Prod.mk _) _ _ x _ => return x
      | xy => return .proj ``Prod 0 xy
    | .proj ``Prod 1 xy =>
      match (← normalizeCore xy) with
      | mkApp4 (.const ``Prod.mk _) _ _ _ y => return y
      | xy => return .proj ``Prod 1 xy
    | (mkApp3 (.const ``Prod.fst lvl) X Y xy) =>
      match (← normalizeCore xy) with
      | mkApp4 (.const ``Prod.mk _) _ _ x _ => return x
      | xy => return (mkApp3 (.const ``Prod.fst lvl) X Y xy)
    | (mkApp3 (.const ``Prod.snd lvl) X Y xy) =>
      match (← normalizeCore xy) with
      | mkApp4 (.const ``Prod.mk _) _ _ _ y => return y
      | xy => return (mkApp3 (.const ``Prod.snd lvl) X Y xy)
    | .app f x => do
      return .app (← normalizeCore f) (← normalizeCore x)
    | .lam n t b bi =>
      return .lam n t (← normalizeCore b) bi
    | .mdata d e =>
      return .mdata d (← normalizeCore e)
    | e => return e


def normalize (e : Expr) : DataSynthM (Simp.Result) := do

  withMainTrace
    (fun _ => return m!"normalization") do

  let cfg := (← read).config

  -- some of the normalization procedures do not work with meta variables
  let e ← instantiateMVars e
  let e₀ := e
  let mut e := e

  if cfg.normalizeLet' then
    e ← normalizeLet' e

  if cfg.normalizeLet then
    e := splitLet e

  -- this looks like the best option right now
  if cfg.norm_core then
    e ← normalizeCore e

  if cfg.norm_dsimp then
    e ← Simp.dsimp e

  let mut r : Simp.Result := { expr := e }

  if cfg.norm_lsimp then
    r ← r.mkEqTrans (← Simp.lsimp r.expr)

  if cfg.norm_simp then
    r ← r.mkEqTrans (← Simp.simp r.expr)

  -- report only when something has been done
  if ¬(e₀==r.expr) then
    trace[Meta.Tactic.data_synth.normalize] m!"\n{e₀}\n==>\n{r.expr}"

  -- user specified normalization
  r ← r.mkEqTrans (← (← read).normalize r.expr)

  return r


def Result.normalize (r : Result) : DataSynthM Result := do
  withProfileTrace "normalize result" do
  r.congr (← r.xs.mapM (fun x => instantiateMVars x >>= DataSynth.normalize ))


def Goal.getCandidateTheorems (g : Goal) : DataSynthM (Array DataSynthTheorem) := do
  let (_,e) ← g.mkFreshProofGoal
  let ext := dataSynthTheoremsExt.getState (← getEnv)
  -- let keys ← Mathlib.Meta.FunProp.RefinedDiscrTree.mkDTExpr e {}
  -- trace[Meta.Tactic.data_synth] "keys: {keys}"
  let thms ← ext.theorems.getMatchWithScore e false {} -- {zeta:=false, zetaDelta:=false}
  let thms := thms |>.map (·.1) |>.flatten |>.qsort (fun x y => x.priority > y.priority)
  return thms


def isDataSynthGoal? (e : Expr) : MetaM (Option Goal) := do

  let .some dataSynthDecl ← isDataSynth? e | return none

  let fn := e.getAppFn'
  let args := e.getAppArgs

  let mut outArgs := Array.mkArray args.size false
  for i in dataSynthDecl.outputArgs do
    outArgs := outArgs.set! i true

  let e' ← go fn args.toList outArgs.toList #[]

  return some {
    goal := e'
    dataSynthDecl := dataSynthDecl
  }
where
  -- replaces out arguments in `e` with free variables
  go (fn : Expr) (args : List Expr) (outArgs : List Bool) (fvars : Array Expr) :=
    match args, outArgs with
    | a :: as, false :: os => go (fn.app a) as os fvars
    | a :: as, true :: os => do
      withLocalDeclD `x (← inferType a) fun var => do
        go (fn.app var) as os (fvars.push var)
    | [], _
    | _ , [] => mkLambdaFVars fvars fn



def Goal.assumption? (goal : Goal) : DataSynthM (Option Result) := do
  withProfileTrace "assumption?" do
  (← getLCtx).findDeclRevM? fun localDecl => do
    forallTelescope localDecl.type fun xs type => do
    if localDecl.isImplementationDetail then
      return none
    else if type.isAppOf' goal.dataSynthDecl.name then
      let (_,e) ← goal.mkFreshProofGoal
      let (ys, _, type') ← forallMetaTelescope localDecl.type
      if (← isDefEq e type') then
        return ← goal.getResultFrom (mkAppN (.fvar localDecl.fvarId) ys)
      else
        return none
    else
      return none


def discharge? (e : Expr) : DataSynthM (Option Expr) := do
  (← read).discharge e


def synthesizeArgument (x : Expr) : DataSynthM Bool := do
  let x ← instantiateMVars x
  let X ← inferType x

  -- skip if already synthesized
  unless x.isMVar do return true
  withProfileTrace "synthesizeArgument" do


  let b ← forallTelescope X fun ys X => do
    if let .some g ← isDataSynthGoal? X then
      -- try recursive call
      if let .some r ← do dataSynth g then
        x.mvarId!.assignIfDefeq (← mkLambdaFVars ys r.proof)
        return true

      if let some r ← g.assumption? then
        x.mvarId!.assignIfDefeq (← mkLambdaFVars ys r.proof)
        return true

    return false
  if b then return true

  -- type class synthesis
  if let .some _ ← isClass? X then
    try
      let inst ← synthInstance X
      x.mvarId!.assignIfDefeq inst
      return true
    catch _ =>
      return false

  -- try assumptions
  if (← inferType X).isProp then
    try
      x.mvarId!.assumption
      return true
    catch _ =>
      pure ()

  if let .some prf ← discharge? X then
    if ← isDefEq (← inferType prf) X then
      x.mvarId!.assignIfDefeq prf
      return true

  return false


/-
 -/
def tryTheorem? (e : Expr) (thm : DataSynthTheorem) : DataSynthM (Option Expr) := do

  withMainTrace
    (fun r => return m!"[{ExceptToEmoji.toEmoji r}] applying {← ppOrigin (.decl thm.thmName)}") do

  let thmProof ← thm.getProof
  let type ← inferType thmProof
  let (xs, _, type) ← forallMetaTelescope type
  let thmProof := thmProof.beta xs

  unless (← isDefEq e type) do
    trace[Meta.Tactic.data_synth] "unification failed\n{e}\n=?=\n{type}"
    return none

  -- todo: redo this, make a queue of all argument an try synthesize them over and over, until done or no progress
  -- try to synthesize all arguments
  for x in xs do
    let _ ← synthesizeArgument x

  -- check if all arguments have been synthesized
  for x in xs do
    let x ← instantiateMVars x
    if x.isMVar then
      trace[Meta.Tactic.data_synth] "failed to synthesize argument {x} : {← inferType x}"
      return none

  return some thmProof


def Goal.tryTheorem? (goal : Goal) (thm : DataSynthTheorem) : DataSynthM (Option Result) := do
  withProfileTrace "tryTheorem" do

  let (xs, e) ← goal.mkFreshProofGoal

  let .some prf ← DataSynth.tryTheorem? e thm | return none

  let mut r := Result.mk xs prf goal

  r ← r.normalize

  return r



-- main function that looks up theorems
partial def main (goal : Goal) : DataSynthM (Option Result) := do
  withProfileTrace "main" do

  let thms ← goal.getCandidateTheorems

  trace[Meta.Tactic.data_synth] "candidates {thms.map (fun t => t.thmName)}"

  for thm in thms do
    if let .some r ← goal.tryTheorem? thm then
      return r

  -- try local theorems
  if let some r ← goal.assumption? then
    return r

  return none


def mainCached (goal : Goal) (initialTrace := true) : DataSynthM (Option Result) := do

  let go := do
    match (← get).cache[goal]? with
    | some r =>
      trace[Meta.Tactic.data_synth] "using cached result"
      return r
    | none =>
      match ← main goal with
      | some r =>
        modify (fun s => {s with cache := s.cache.insert goal r})
        return r
      | none =>
        modify (fun s => {s with failedCache := s.failedCache.insert goal})
        return none

  if initialTrace then
    withMainTrace
      (fun r =>
        match r with
        | .ok (some _r) => return m!"[✅] {← goal.pp}"
        | .ok none => return m!"[❌] {← goal.pp}"
        | .error e => return m!"[💥️] {← goal.pp}\n{e.toMessageData}")
      go
  else
    go


def Goal.getInputFun? (g : Goal) : MetaM (Option Expr) := do
  let some i := g.dataSynthDecl.inputArg | return none
  lambdaTelescope g.goal fun _ b => do
    return b.getArg! i


--------------------------------------------------------------------------------------------------

/-- Given goal for composition `f∘g` and given `f` and `g` return corresponding goals for `f` and `g` -/
def compGoals (fgGoal : DataSyntGoal) (f g : Expr) : DataSynthM (Option (Goal×Goal)) := return none

/-- Given result for `f` and `g` return result for `f∘g` -/
def compResults (hf hg : DataySynthResult) : DataSynthM (Option Result) := return none


-- theorem name, gId, fId, hgId, hfId
def letTheorems : Std.HashMap Name (Name × Nat × Nat × Nat × Nat) :=
  Std.HashMap.empty
    |>.insert `HasFwdDerivAt (`HasFwdDerivAt.let_rule, 3, 4, 8, 9)
    |>.insert `SciLean.HasFwdFDerivAt (`SciLean.HasFwdFDerivAt.let_rule, 11, 12, 16, 17)
    |>.insert `SciLean.HasRevFDeriv (`SciLean.HasRevFDeriv.let_rule, 14, 15, 18, 19)
    |>.insert `SciLean.HasRevFDerivUpdate (`SciLean.HasRevFDerivUpdate.let_rule, 14, 15, 18, 19)
    |>.insert `SciLean.RealToFloatFun (`SciLean.RealToFloatFun.let_rule, 9, 10, 13, 14)


/-- Given goal for composition `fun x => let y:=g x; f y x` and given `f` and `g` return corresponding goals for `↿f` and `g` -/
def letGoals (fgGoal : Goal) (f g  : Expr) : DataSynthM (Option (Goal×Goal)) := do
  withProfileTrace "letGoals" do

  let some (thmName, gId, fId, hgId, hfId) := letTheorems[fgGoal.dataSynthDecl.name]?
    | return none

  let info ← getConstInfo thmName
  let (xs, _, thm) ← forallMetaTelescope info.type

  try
    withMainTrace (fun _ => return m!"assigning data") do
    xs[gId]!.mvarId!.assignIfDefeq g
  catch e =>
    throwError s!"{← ppExpr (xs[gId]!)} : {← ppExpr (← inferType xs[gId]!)} := {← ppExpr g}"

  try
    withMainTrace (fun _ => return m!"assigning data") do
    xs[fId]!.mvarId!.assignIfDefeq f
  catch e =>
    throwError s!"{← ppExpr (xs[fId]!)} : {← ppExpr (← inferType xs[fId]!)} := {← ppExpr f}"


  let (_,rhs) ← fgGoal.mkFreshProofGoal
  if ¬(← isDefEq thm rhs) then
    return none

  let hg ← inferType xs[hgId]! >>= instantiateMVars
  let hf ← inferType xs[hfId]! >>= instantiateMVars
  let some ggoal ← isDataSynthGoal? hg | return none
  let some fgoal ← isDataSynthGoal? hf | return none
  return (fgoal, ggoal)

/-- Given result for `↿f` and `g` return result for `fun x => let y:=g x; f y x` -/
def letResults (fgGoal : Goal) (f g : Expr) (hf hg : Result) : DataSynthM (Option Result) := do
  withProfileTrace "letResults" do

  let some (thmName, gId, fId, hgId, hfId) := letTheorems[fgGoal.dataSynthDecl.name]?
    | return none

  let mut args? : Array (Option Expr) := .mkArray (max hgId hfId+1) none
  args? := args?.set! gId g
  args? := args?.set! fId f
  args? := args?.set! hgId hg.proof
  args? := args?.set! hfId hf.proof

  let proof ← mkAppOptM thmName args?
  let r ← fgGoal.getResultFrom proof
  return r

/-- Given goal for composition `fun x i => f x i` and given free var `i` and `f` return goal for `(f · i)` -/
def piGoal (fGoal : DataSyntGoal) (i : Expr) (fi : Expr) : DataSynthM (Option Goal) := return none

/-- Given result for `(f · i)` and free variable `i` return result for `f`-/
def piResult (hf : Result) (i : Expr) : DataSynthM (Option Result) := return none


-- theorem name, fId, gId, p₁Id, p₂Id, qId, hgId
def projTheorems : Std.HashMap Name (Name × Nat × Nat × Nat × Nat × Nat × Nat) :=
  Std.HashMap.empty
    |>.insert `SciLean.HasRevFDeriv (`SciLean.HasRevFDeriv.proj_rule, 13, 15, 16, 17, 18, 19)
    |>.insert `SciLean.HasRevFDerivUpdate (`SciLean.HasRevFDerivUpdate.proj_rule, 12, 14, 15, 16, 17, 18)

def projGoals (fGoal : Goal) (f g p₁ p₂ q : Expr) : DataSynthM (Option Goal) := do
  withProfileTrace "projGoals" do

  let some (thmName, fId, gId, p₁Id, p₂Id, qId, hgId) := projTheorems[fGoal.dataSynthDecl.name]?
    | return none

  let info ← getConstInfo thmName
  let (xs, _, thm) ← forallMetaTelescope info.type

  xs[fId]!.mvarId!.assignIfDefeq f
  xs[gId]!.mvarId!.assignIfDefeq g
  xs[p₁Id]!.mvarId!.assignIfDefeq p₁
  xs[p₂Id]!.mvarId!.assignIfDefeq p₂
  xs[qId]!.mvarId!.assignIfDefeq q

  let (_,rhs) ← fGoal.mkFreshProofGoal
  if ¬(← isDefEq thm rhs) then
    return none

  let hg ← inferType xs[hgId]! >>= instantiateMVars
  let some ggoal ← isDataSynthGoal? hg | return none
  return some ggoal

/-- Given result for `↿f` and `g` return result for `fun x => let y:=g x; f y x` -/
def projResults (fGoal : Goal) (f g p₁ p₂ q : Expr) (hg : Result) : DataSynthM (Option Result) := do
  withProfileTrace "projResults" do

  let some (thmName, fId, gId, p₁Id, p₂Id, qId, hgId) := projTheorems[fGoal.dataSynthDecl.name]?
    | return none

  let mut args? : Array (Option Expr) := .mkArray (hgId+1) none
  args? := args?.set! fId f
  args? := args?.set! gId g
  args? := args?.set! p₁Id p₁
  args? := args?.set! p₂Id p₂
  args? := args?.set! qId q
  args? := args?.set! hgId hg.proof

  let proof ← mkAppOptM thmName args?
  let r ← fGoal.getResultFrom proof
  return r


def constCase? (goal : Goal) (f : FunData) : DataSynthM (Option Result) := do

  -- todo: this work of checking free variables should be shared with `decomposeDomain?`
  --       Maybe `FunData` should carry a `FVarSet`
  let vars := (← f.body.collectFVars |>.run {}).2.fvarSet
  let (xs₁, _) := f.xs.split (fun x => vars.contains x.fvarId!)

  unless xs₁.size = 0 do return none
  withProfileTrace "const case" do
  withMainTrace (fun _ => return "constant function") do

  let thm : DataSynthTheorem ←
     getTheoremFromConst (goal.dataSynthDecl.name.append `const_rule)

  goal.tryTheorem? thm


def decomposeDomain? (goal : Goal) (f : FunData) : DataSynthM (Option Result) := do
  if ¬(← read).config.domainDec then
    return none
  let some (p₁,p₂,q,g) ← f.decomposeDomain? | return none
  withProfileTrace "decomposeDomain" do
  withMainTrace (fun r => pure m!"[{ExceptToEmoji.toEmoji r}] domain projection {p₁}") do
    let some ggoal ← projGoals goal (← f.toExpr) (← g.toExpr) p₁ p₂ q | return none
    let some hg ← dataSynthFun ggoal g | return none
    let some r ← projResults goal (← f.toExpr) (← g.toExpr) p₁ p₂ q hg | return none
    let r ← r.normalize
    return r


def compCase (goal : Goal) (f g : FunData) : DataSynthM (Option Result) := do
  withProfileTrace "comp case" do
  let some (fgoal, ggoal) ← compGoals goal (← f.toExpr) (← g.toExpr) | return none
  let some hg ← dataSynthFun ggoal g | return none
  let some hf ← dataSynthFun fgoal f | return none
  let r ← compResults hf hg
  return r


def letCase (goal : Goal) (f g : FunData) : DataSynthM (Option Result) := do
  withProfileTrace "letCase" do
  let some (fgoal, ggoal) ← letGoals goal (← f.toExprCurry1) (← g.toExpr) | return none
  let some hg ←
    withProfileTrace "solving g" do
    dataSynthFun ggoal g | return none
  let some hf ←
    withProfileTrace "solving f" do
    dataSynthFun fgoal f | return none
  let some r ← letResults goal (← f.toExprCurry1) (← g.toExpr) hf hg | return none
  let r ← r.normalize
  return r

def lamCase (goal : Goal) (f : FunData) : DataSynthM (Option Result) := do
  withProfileTrace "lamCase" do
  lambdaBoundedTelescope f.body 1 fun is b => do
    let i := is[0]!
    let fi := {f with body := f.body.beta is}
    let some figoal ← piGoal goal i (← fi.toExpr) | return none
    let some hfi ← dataSynthFun figoal fi | return none
    let some r ← piResult hfi i | return none
    let r ← r.normalize
    return r


/-- Similar to `dataSynth` but driven by function. -/
partial def mainFun (goal : Goal) (f : FunData) : DataSynthM (Option Result) := do
  withProfileTrace "mainFun" do

  -- spacial case for constant functions
  if let some r ← constCase? goal f then
    return r

  -- decompose domain if possible
  if let some r ← decomposeDomain? goal f then
    return r

  let h ← f.funHead
  trace[Meta.Tactic.data_synth] "function case {repr h}"

  match h with
  | .app => mainCached goal (initialTrace:=false)
  | .fvar n => mainCached goal (initialTrace:=false)
  | .bvar n => mainCached goal (initialTrace:=false)
  | .letE =>
    match ← f.decompose with
    | .comp f g => compCase goal f g
    | .letE f g => letCase goal f g
    | _ => return none
  | .lam => lamCase goal f
  | _ => return none


def mainFunCached (goal : Goal) (f : FunData) : DataSynthM (Option Result) := do

  withMainTrace
    (fun r =>
      match r with
      | .ok (some r) => return m!"[✅] {← goal.pp}"
      | .ok none => return m!"[❌] {← goal.pp}"
      | .error e => return m!"[💥️] {← goal.pp}\n{e.toMessageData}") do

  trace[Meta.Tactic.data_synth.input] "{← f.pp}"

  match (← get).cache[goal]? with
  | some r =>
    trace[Meta.Tactic.data_synth] "using cached result"
    return r
  | none =>
    match ← mainFun goal f with
    | some r =>
      modify (fun s => {s with cache := s.cache.insert goal r})
      return r
    | none =>
      modify (fun s => {s with failedCache := s.failedCache.insert goal})
      return none


def dataSynthImpl (goal : Goal) : DataSynthM (Option Result) := do
  if let .some f ← goal.getInputFun? then
    mainFunCached goal (← getFunData f)
  else
    mainCached goal

initialize dataSynthRef.set dataSynthImpl


def dataSynthFunImpl (goal : Goal) (f : FunData) : DataSynthM (Option Result) := do
  mainFunCached goal f

initialize dataSynthFunRef.set dataSynthFunImpl


initialize registerTraceClass `Meta.Tactic.data_synth
initialize registerTraceClass `Meta.Tactic.data_synth.input
initialize registerTraceClass `Meta.Tactic.data_synth.normalize
initialize registerTraceClass `Meta.Tactic.data_synth.profile
