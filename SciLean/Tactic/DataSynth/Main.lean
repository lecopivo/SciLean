import SciLean.Tactic.DataSynth.Types
import SciLean.Tactic.DataSynth.Theorems
import Batteries.Tactic.Exact

namespace SciLean.Tactic.DataSynth

open Lean Meta


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

partial def flattenLet (e : Expr) : Expr :=
  match e with
  | .letE n2 t2 (.letE n1 t1 v1 v2 ndep1) b ndep2 =>
    let b := b.liftLooseBVars 1 1
    flattenLet <| .letE n1 t1 v1 (.letE n2 t2 v2 b ndep2) ndep1
  | .letE n t v b ndep =>
    .letE n t v (flattenLet b) ndep
  | _ => e


def reduceProdProj (e : Expr) : Expr :=
  match e with
  | mkApp3 (.const ``Prod.fst lvl) X Y xy =>
    match reduceProdProj xy with
    | (mkApp4 (.const ``Prod.mk _) _ _ x _) => x
    | xy => mkApp3 (.const ``Prod.fst lvl) X Y xy
  | mkApp3 (.const ``Prod.snd lvl) X Y xy =>
    match reduceProdProj xy with
    | (mkApp4 (.const ``Prod.mk _) _ _ _ y) => y
    | xy => mkApp3 (.const ``Prod.snd lvl) X Y xy
  | _ => e


open Lean Meta in
partial def splitLet (e : Expr) : Expr :=
  match e with
  | .letE n t v b ndep =>

  -- | .letE n2 t2 (.letE n1 t1 v1 v2 ndep1) b ndep2 =>
  --   let b := b.liftLooseBVars 1 1
  --   flattenLet <| .letE n1 t1 v1 (.letE n2 t2 v2 b ndep2) ndep1

    match v with
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

    | (mkApp3 (.const ``Prod.fst _) ..)
    | (mkApp3 (.const ``Prod.snd _) ..) =>
      let v' := reduceProdProj v
      if v'==v then
        .letE n t v (splitLet b) ndep
      else
        splitLet (.letE n t v' b ndep)

    | v => .letE n t v (splitLet b) ndep

  | .app f x =>
    .app (splitLet f) (splitLet x)
  | .lam n t b bi =>
    .lam n t (splitLet b) bi
  | _ => e


def normalize (e : Expr) : DataSynthM (Simp.Result) := do

  withTraceNode
    `Meta.Tactic.data_synth
    (fun _ => return m!"normalization") do

  let cfg := (← read).config

  let e₀ := e
  let mut e := e

  -- fast let normalization
  if cfg.normalizeLet then
    e ← lambdaTelescope e fun xs b => do
      mkLambdaFVars xs (splitLet (b))

  let mut r : Simp.Result := { expr := e }

  if cfg.lsimp then
    r ← r.mkEqTrans (← Simp.lsimp r.expr)

  if cfg.simp then
    r ← r.mkEqTrans (← Simp.simp r.expr)

  -- report only when something has been done
  if ¬(e₀==r.expr) then
    trace[Meta.Tactic.data_synth.normalize] m!"\n{e₀}\n==>\n{r.expr}"

  -- todo run normalization from context

  return r


def discharge? (e : Expr) : DataSynthM (Option Expr) := do
  (← read).discharge e

def Goal.getCandidateTheorems (g : Goal) : DataSynthM (Array DataSynthTheorem) := do
  let (_,e) ← g.mkFreshProofGoal
  let ext := dataSynthTheoremsExt.getState (← getEnv)
  -- let keys ← Mathlib.Meta.FunProp.RefinedDiscrTree.mkDTExpr e {}
  -- trace[Meta.Tactic.data_synth] "keys: {keys}"
  let thms ← ext.theorems.getMatchWithScore e false {} -- {zeta:=false, zetaDelta:=false}
  let thms := thms |>.map (·.1) |>.flatten |>.qsort (fun x y => x.priority > y.priority)
  return thms

def replaceMVarsWithFVars (e : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  let fn := e.getAppFn'
  let args := e.getAppArgs'
  go fn args.toList #[]
where
  go (e : Expr) (args : List Expr) (fvars : Array Expr) : MetaM α := do
  match args with
  | [] => k fvars e
  | a :: as =>
    if ¬(← instantiateMVars a).isMVar then
      go (e.app a) as fvars
    else
      let type := (← inferType e).bindingDomain!
      let name := Name.mkSimple (String.stripPrefix s!"{← ppExpr a}" "?")
      withLocalDeclD name type fun x => do
        go (e.app x) as (fvars.push x)


def isDataSynthGoal? (e : Expr) : MetaM (Option Goal) := do

  let .some dataSynthDecl ← isDataSynth? e | return none

  let goal ← replaceMVarsWithFVars (← instantiateMVars e) mkLambdaFVars

  return some { goal := goal, dataSynthDecl := dataSynthDecl }

def synthesizeArgument (x : Expr) : DataSynthM Bool := do

  let x ← instantiateMVars x
  let X ← inferType x

  -- skip if already synthesized
  unless x.isMVar do return true

  if let .some g ← isDataSynthGoal? X then
    -- try recursive call
    if let .some r ← do dataSynth g then
      x.mvarId!.assignIfDefeq r.proof
      return true

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

  withTraceNode
    `Meta.Tactic.data_synth
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

  for x in xs do
    let _ ← synthesizeArgument x

  -- check if all arguments have been synthesized
  for x in xs do
    let x ← instantiateMVars x
    if x.isMVar then
      trace[Meta.Tactic.data_synth] "failed to synthesize argument {x} : {← inferType x}"
      return none

  return some thmProof

-- main function that looks up theorems
partial def main (goal : Goal) : DataSynthM (Option Result) := do

  let thms ← goal.getCandidateTheorems

  if thms.size = 0 then
    trace[Meta.Tactic.data_synth] "no applicable theorems"
    return none

  for thm in thms do
    -- for each theorem we generate a fresh data mvars `xs` because them might get partially filled
    -- when unsuccesfully trying a theorem
    let (xs, e) ← goal.mkFreshProofGoal
    if let .some prf ← tryTheorem? e thm  then
      -- result
      let r := Result.mk xs prf goal

      -- normalize synthsized data
      let rs ← xs.mapM (fun x => instantiateMVars x >>= normalize)

      -- fix proof
      let r ← r.congr rs
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
    withTraceNode `Meta.Tactic.data_synth
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
  lambdaTelescope g.goal fun xs b => do
    let f := b.getArg! i

    -- just check that `f` is not output argument
    if xs.any (f==·) then
      return none
    else
      return f



--------------------------------------------------------------------------------------------------

/-- Given goal for composition `f∘g` and given `f` and `g` return corresponding goals for `f` and `g` -/
def compGoals (fgGoal : DataSyntGoal) (f g : Expr) : DataSynthM (Option (Goal×Goal)) := return none

/-- Given result for `f` and `g` return result for `f∘g` -/
def compResults (hf hg : DataySynthResult) : DataSynthM (Option Result) := return none


private def mkHasFwdDerivAt (f : Expr) (x : Expr) : MetaM (Option Goal) := do

  let some (fX,fY) := (← inferType f).arrow? | return none
  let f' ← mkFreshExprMVar (← mkArrow fX (← mkArrow fX (← mkAppM ``Prod #[fY,fY])))
  let h ← mkAppM `HasFwdDerivAt #[f,f',x]

  let some goal ← isDataSynthGoal? h | return none
  trace[Meta.Tactic.data_synth] "created goal {← goal.pp}"
  return goal


-- theorem name, gId, fId, hgId, hfId
def letTheorems : Std.HashMap Name (Name × Nat × Nat × Nat × Nat) :=
  Std.HashMap.empty
    |>.insert `HasFwdDerivAt (`HasFwdDerivAt.let_rule, 3, 4, 8, 9)
    |>.insert `SciLean.HasFwdFDerivAt (`SciLean.HasFwdFDerivAt.let_rule, 11, 12, 16, 17)
    |>.insert `SciLean.HasRevFDeriv (`SciLean.HasRevFDeriv.let_rule, 14, 15, 18, 19)


/-- Given goal for composition `fun x => let y:=g x; f y x` and given `f` and `g` return corresponding goals for `↿f` and `g` -/
def letGoals (fgGoal : Goal) (f g  : Expr) : DataSynthM (Option (Goal×Goal)) := do

  let some (thmName, gId, fId, hgId, hfId) := letTheorems[fgGoal.dataSynthDecl.name]?
    | return none

  let info ← getConstInfo thmName
  let (xs, _, thm) ← forallMetaTelescope info.type

  xs[gId]!.mvarId!.assignIfDefeq g
  xs[fId]!.mvarId!.assignIfDefeq f

  let rhs := (← fgGoal.mkFreshProofGoal).2
  if ¬(← isDefEq thm rhs) then
    return none

  let hg ← inferType xs[hgId]! >>= instantiateMVars
  let hf ← inferType xs[hfId]! >>= instantiateMVars
  let some ggoal ← isDataSynthGoal? hg | return none
  let some fgoal ← isDataSynthGoal? hf | return none
  return (fgoal, ggoal)

/-- Given result for `↿f` and `g` return result for `fun x => let y:=g x; f y x` -/
def letResults (fgGoal : Goal) (f g : Expr) (hf hg : Result) : DataSynthM (Option Result) := do

  let some (thmName, gId, fId, hgId, hfId) := letTheorems[fgGoal.dataSynthDecl.name]?
    | return none

  let mut args? : Array (Option Expr) := .mkArray (max hgId hfId+1) none
  args? := args?.set! gId g
  args? := args?.set! fId f
  args? := args?.set! hgId hg.proof
  args? := args?.set! hfId hf.proof

  let proof ← mkAppOptM thmName args?
  let Proof ← inferType proof

  -- extract data from the result
  let (xs,g) ← fgGoal.mkFreshProofGoal
  if ¬(← isDefEq g Proof) then
    return none
  let xs ← xs.mapM instantiateMVars

  let r : Result := {
    xs := xs
    proof := ← instantiateMVars proof
    goal := fgGoal
  }

  -- normalize all output data
  let r ← r.congr (← xs.mapM normalize)

  return r


/-- Given goal for composition `fun x i => f x i` and given free var `i` and `f` return goal for `(f · i)` -/
def piGoal (fGoal : DataSyntGoal) (i : Expr) (fi : Expr) : DataSynthM (Option Goal) := return none

/-- Given result for `(f · i)` and free variable `i` return result for `f`-/
def piResult (hf : Result) (i : Expr) : DataSynthM (Option Result) := return none


/-- Similar to `dataSynth` but driven by function. -/
partial def mainFun (goal : Goal) (f : FunData) : DataSynthM (Option Result) := do

  let h ← f.funHead
  trace[Meta.Tactic.data_synth] "function case {repr h}"

  match ← f.funHead with
  | .app => mainCached goal (initialTrace:=false)
  | .fvar n => mainCached goal (initialTrace:=false)
  | .bvar n => mainCached goal (initialTrace:=false)
  | .letE =>
    match ← f.decompose with
    | .comp f g =>
      let some (fgoal, ggoal) ← compGoals goal (← f.toExpr) (← g.toExpr) | return none
      let some hg ← dataSynthFun ggoal g | return none
      let some hf ← dataSynthFun fgoal f | return none
      compResults hf hg -- normalize
    | .letE f g =>
      let some (fgoal, ggoal) ← letGoals goal (← f.toExprCurry1) (← g.toExpr) | return none
      let some hg ← dataSynthFun ggoal g | return none
      let some hf ← dataSynthFun fgoal f | return none
      letResults goal (← f.toExprCurry1) (← g.toExpr) hf hg
    | _=> return none
  | .lam =>
    lambdaBoundedTelescope f.body 1 fun is b => do
      let i := is[0]!
      let fi := {f with body := f.body.beta is}
      let some figoal ← piGoal goal i (← fi.toExpr) | return none
      let some hfi ← dataSynthFun figoal fi | return none
      piResult hfi i -- normalize
  | _ => return none




def mainFunCached (goal : Goal) (f : FunData) : DataSynthM (Option Result) := do

  withTraceNode `Meta.Tactic.data_synth
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
