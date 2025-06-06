import SciLean.Tactic.DataSynth.Types
import SciLean.Tactic.DataSynth.Theorems
import Batteries.Tactic.Exact

import Lean.Meta.Transform

set_option linter.unusedVariables false

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
     | mkApp3 (.const ``Prod.fst _) _ _ (mkApp4 (.const ``Prod.mk _) _ _ x _y) =>
       return .done x
     | mkApp3 (.const ``Prod.snd _) _ _ (mkApp4 (.const ``Prod.mk _) _ _ _x y) =>
       return .done y
     | .proj ``Prod 0 (mkApp4 (.const ``Prod.mk _) _ _ x _y) =>
       return .done x
     | .proj ``Prod 1 (mkApp4 (.const ``Prod.mk _) _ _ _x y) =>
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
      | .letE n t v b nonDep => normalizeCore (.letE n t v (.proj ``Prod 0 b) nonDep)
      | xy => return .proj ``Prod 0 xy
    | .proj ``Prod 1 xy =>
      match (← normalizeCore xy) with
      | mkApp4 (.const ``Prod.mk _) _ _ _ y => return y
      | .letE n t v b nonDep => normalizeCore (.letE n t v (.proj ``Prod 1 b) nonDep)
      | xy => return .proj ``Prod 1 xy
    | (mkApp3 (.const ``Prod.fst lvl) X Y xy) =>
      match (← normalizeCore xy) with
      | mkApp4 (.const ``Prod.mk _) _ _ x _ => return x
      | .letE n t v b nonDep => normalizeCore (.letE n t v (mkApp3 (.const ``Prod.fst lvl) X Y b) nonDep)
      | xy => return (mkApp3 (.const ``Prod.fst lvl) X Y xy)
    | (mkApp3 (.const ``Prod.snd lvl) X Y xy) =>
      match (← normalizeCore xy) with
      | mkApp4 (.const ``Prod.mk _) _ _ _ y => return y
      | .letE n t v b nonDep => normalizeCore (.letE n t v (mkApp3 (.const ``Prod.snd lvl) X Y b) nonDep)
      | xy => return (mkApp3 (.const ``Prod.snd lvl) X Y xy)
    | .app f x => do
      let f' ← normalizeCore f
      let x' ← normalizeCore x
      if f==f' ∧ x==x' then
        return .app f x
      else
        match f', x' with
        | .letE n t v b nonDep, x => normalizeCore (.letE n t v (.app b (x.liftLooseBVars 0 1)) nonDep)
        | f, .letE n t v b nonDep => normalizeCore (.letE n t v (.app (f.liftLooseBVars 0 1) b) nonDep)
        | f, x => normalizeCore (.app f x)
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


def Goal.getCandidateTheorems (g : Goal) : DataSynthM (Array GeneralTheorem) := do
  let (_,e) ← g.mkFreshProofGoal
  let ext := dataSynthTheoremsExt.getState (← getEnv)
  let keys ← Lean.Meta.RefinedDiscrTree.mkDTExpr e
  trace[Meta.Tactic.data_synth] "keys: {keys}"
  let thms ← ext.theorems.getMatchWithScore e false -- {zeta:=false, zetaDelta:=false}
  let thms := thms |>.map (·.1) |>.flatten |>.qsort (fun x y => x.priority > y.priority)
  return thms


def isDataSynthGoal? (e : Expr) : MetaM (Option Goal) := do

  let .some dataSynthDecl ← isDataSynth? e | return none

  let fn := e.getAppFn'
  let args := e.getAppArgs

  let mut outArgs := Array.replicate args.size false
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
    forallTelescope localDecl.type fun _xs type => do
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

def synthesizeAutoParam (x X : Expr) : DataSynthM Bool := do
  let .some (.const tacticDecl ..) := X.getAutoParamTactic?
    | return false
  let env ← getEnv
  match Lean.Elab.evalSyntaxConstant env (← getOptions) tacticDecl with
  | .error err       => throwError err
  | .ok tacticSyntax =>
    let X' := X.appFn!.appArg! -- extract the actual type from `autoParam _ _`
    let disch := Mathlib.Meta.FunProp.tacticToDischarge ⟨tacticSyntax⟩
    trace[Meta.Tactic.data_synth] "calling auto param tactic {tacticSyntax.prettyPrint} to prove {X'}"
    let some r ← disch X' | return false
    try
      x.mvarId!.assignIfDefEq r
      trace[Meta.Tactic.data_synth] "auto param success"
      return true
    catch _e =>
      trace[Meta.Tactic.data_synth] "auto param failed"
      return false

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
        try
          x.mvarId!.assignIfDefEq (← mkLambdaFVars ys r.proof)
          return true
        catch e =>
          trace[Meta.Tactic.data_synth] m!"failed to assign {(← mkLambdaFVars ys r.proof)} to {x}"
          trace[Meta.Tactic.data_synth] e.toMessageData
          pure ()

      if let some r ← g.assumption? then
        try
          x.mvarId!.assignIfDefEq (← mkLambdaFVars ys r.proof)
          return true
        catch e =>
          trace[Meta.Tactic.data_synth] m!"failed to assign {(← mkLambdaFVars ys r.proof)} to {x}"
          trace[Meta.Tactic.data_synth] e.toMessageData
          pure ()

    return false
  if b then return true

  -- type class synthesis
  if let .some _ ← isClass? X then
    try
      let inst ← synthInstance X
      x.mvarId!.assignIfDefEq inst
      return true
    catch _ =>
      pure ()

  -- try auto param
  if X.isAppOfArity' ``autoParam 2 then
    if ← synthesizeAutoParam x X then
      return true

  -- try assumptions
  if (← inferType X).isProp then
    try
      x.mvarId!.assumption
      return true
    catch _ =>
      pure ()

  -- try discharger
  if (← inferType X).isProp then
    if let .some prf ← discharge? X then
      if ← isDefEq (← inferType prf) X then
        try
          x.mvarId!.assignIfDefEq prf
          return true
        catch _ =>
          trace[Meta.Tactic.data_synth] m!"failed to assign {prf} to {x}"
          pure ()

  return false


/- Apply theorem `thm` to solve `e`.

You can provide certain theorem arguments explicitelly with `hint` i.e. for `hint = #[(id₁,e₁),...]`
we assign `eᵢ` to `idᵢ`-th argument of theorem `thm`.

Hints `hintPre` are applied before unification of `e` with theorem statement and `hintPost` are
applied after unification.
 -/
def tryTheorem? (e : Expr) (thm : Theorem) (hintPre hintPost : Array (Nat×Expr) := #[]) : DataSynthM (Option Expr) := do

  withMainTrace
    (fun r => return m!"[{ExceptToEmoji.toEmoji r}] applying {← ppOrigin (.decl thm.thmName)}") do

  let thmProof ← thm.getProof
  let type ← inferType thmProof
  let (xs, _, type) ← forallMetaTelescope type
  let thmProof := thmProof.beta xs

  let argNames ← getConstArgNames thm.thmName
  for (id, arg) in hintPre do
    let mvarId := xs[id]!.mvarId!
    if ¬(← mvarId.isAssigned) then
      try
        mvarId.assignIfDefEq arg
        trace[Meta.Tactic.data_synth] "setting {argNames[id]!} to {arg}"
      catch _e =>
        trace[Meta.Tactic.data_synth] "failed to set {Expr.mvar mvarId} to {arg}"
        return none

  unless (← isDefEq e type) do
    trace[Meta.Tactic.data_synth] "unification failed\n{e}\n=?=\n{type}"
    return none

  for (id, arg) in hintPost do
    let mvarId := xs[id]!.mvarId!
    if ¬(← mvarId.isAssigned) then
      try
        mvarId.assignIfDefEq arg
        trace[Meta.Tactic.data_synth] "setting {argNames[id]!} to {arg}"
      catch _e =>
        trace[Meta.Tactic.data_synth] "failed to set {Expr.mvar mvarId} to {arg}"
        return none

  -- todo: redo this, make a queue of all argument an try synthesize them over and over, until done or no progress
  -- try to synthesize all arguments
  for x in xs do
    let _ ← synthesizeArgument x

  -- check if all arguments have been synthesized
  for x in xs do
    let x ← instantiateMVars x
    if x.isMVar then
      logError m!"failed to synthesize argument {← inferType x} when applying {(← ppOrigin (.decl thm.thmName))}"
      trace[Meta.Tactic.data_synth] "failed to synthesize argument {x} : {← inferType x}"
      return none

  return some thmProof

/-- Same as `tryTheorem?` but post hints are lazily evaluated only after unification succeded! -/
def tryTheorem?' (e : Expr) (thm : Theorem)
    (hintPre : Array (Nat×Expr)) (hintPost : DataSynthM (Option (Array (Nat×Expr)))) : DataSynthM (Option Expr) := do

  withMainTrace
    (fun r => return m!"[{ExceptToEmoji.toEmoji r}] applying {← ppOrigin (.decl thm.thmName)}") do

  let thmProof ← thm.getProof
  let type ← inferType thmProof
  let (xs, _, type) ← forallMetaTelescope type
  let thmProof := thmProof.beta xs

  let argNames ← getConstArgNames thm.thmName
  for (id, arg) in hintPre do
    let mvarId := xs[id]!.mvarId!
    if ¬(← mvarId.isAssigned) then
      try
        mvarId.assignIfDefEq arg
        trace[Meta.Tactic.data_synth] "setting {argNames[id]!} to {arg}"
      catch _e =>
        trace[Meta.Tactic.data_synth] "failed to set {Expr.mvar mvarId} to {arg}"
        return none

  unless (← isDefEq e type) do
    trace[Meta.Tactic.data_synth] "unification failed\n{e}\n=?=\n{type}"
    return none

  let .some hintPost ← hintPost | return none
  for (id, arg) in hintPost do
    let mvarId := xs[id]!.mvarId!
    if ¬(← mvarId.isAssigned) then
      try
        mvarId.assignIfDefEq arg
        trace[Meta.Tactic.data_synth] "setting {argNames[id]!} to {arg}"
      catch _e =>
        trace[Meta.Tactic.data_synth] "failed to set {Expr.mvar mvarId} to {arg}"
        return none

  -- todo: redo this, make a queue of all argument an try synthesize them over and over, until done or no progress
  -- try to synthesize all arguments
  for x in xs do
    let _ ← synthesizeArgument x

  -- check if all arguments have been synthesized
  for x in xs do
    let x ← instantiateMVars x
    if x.isMVar then
      logError m!"failed to synthesize argument {← inferType x} when applying {(← ppOrigin (.decl thm.thmName))}"
      trace[Meta.Tactic.data_synth] "failed to synthesize argument {x} : {← inferType x}"
      return none

  let thmProof ← instantiateMVars thmProof

  if thmProof.hasMVar then
    let mvars := (e.collectMVars {}).result
    if h : 0 < mvars.size then
      throwError m!"proof contains mvar {mvars[0]}"
    let valLvlMVars := (collectLevelMVars {} e).result
    if h : 0 < valLvlMVars.size then
      throwError m!"proof contains level mvar {Level.mvar valLvlMVars[0]}"
    trace[Meta.Tactic.data_synth] "bug in data_synth"

  return some thmProof



def Goal.tryTheorem? (goal : Goal) (thm : Theorem) (hintPre hintPost : Array (Nat×Expr) := #[]) : DataSynthM (Option Result) := do
  withProfileTrace "tryTheorem" do

  let (xs, e) ← goal.mkFreshProofGoal

  let .some prf ← DataSynth.tryTheorem? e thm hintPre hintPost | return none

  let mut r := Result.mk xs prf goal

  r ← r.normalize

  return r

def Goal.tryTheorem?' (goal : Goal) (thm : Theorem)
    (hintPre : Array (Nat×Expr)) (hintPost : DataSynthM (Option (Array (Nat×Expr)))) : DataSynthM (Option Result) := do
  withProfileTrace "tryTheorem" do

  let (xs, e) ← goal.mkFreshProofGoal

  let .some prf ← DataSynth.tryTheorem?' e thm hintPre hintPost | return none

  let mut r := Result.mk xs prf goal

  r ← r.normalize

  return r


-- main function that looks up theorems
partial def main (goal : Goal) : DataSynthM (Option Result) := do
  withProfileTrace "main" do

  let thms ← -- withConfig (fun cfg => {cfg with zeta:=false, zetaDelta:=false}) <|
    goal.getCandidateTheorems

  trace[Meta.Tactic.data_synth] "candidates {thms.map (fun t => t.thmName)}"
  if thms.size = 0 then
    logError m!"no candidate theorems for {← goal.pp}"

  for thm in thms do
    if let .some r ← goal.tryTheorem? thm.toTheorem then
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
def compGoals (thm : LambdaTheorem) (fgGoal : Goal) (f g : Expr) : DataSynthM (Option (LambdaTheorem×Goal×Goal)) := do
  withProfileTrace "compGoals" do
  -- for thm in thms do
    let .comp gId fId hgId hfId := thm.data | throwError m!"invalid composition theorem {thm.thmName}"
    let info ← getConstInfo thm.thmName

    let args : Array (Option Expr) :=
      Array.replicate (max gId fId) none |>.set! gId g |>.set! fId f

    let (xs, _, statment) ← forallMetaTelescope (← inferType (← thm.getProof))
    try
      withMainTrace (fun _ => return m!"assigning data") do
      xs[gId]!.mvarId!.assignIfDefEq g
    catch _e =>
      throwError s!"failed assigning data {← ppExpr g} to {← ppExpr (xs[gId]!)} of type {← ppExpr (← inferType xs[gId]!)}"

    try
      withMainTrace (fun _ => return m!"assigning data") do
      xs[fId]!.mvarId!.assignIfDefEq f
    catch _e =>
      throwError s!"failed assigning data {← ppExpr (xs[fId]!)} to {← ppExpr (xs[fId]!)} of type {← ppExpr (← inferType xs[fId]!)}"

    let (_,rhs) ← fgGoal.mkFreshProofGoal
    if ¬(← isDefEq statment rhs) then
      trace[Meta.Tactic.data_synth] "failed to unify {← ppExpr statment} =?= {← ppExpr rhs}"
      return none

    -- synthesize any possbile class, there might be `outParam` that nees to be filled by those
    -- classes
    for x in xs do
      if ¬(← x.mvarId!.isAssigned) then
        if let some _ ← isClass? (← inferType x) then
          try
            x.mvarId!.inferInstance
          catch _ =>
            pure ()

    let hg ← inferType xs[hgId]! >>= instantiateMVars
    let hf ← inferType xs[hfId]! >>= instantiateMVars
    trace[Meta.Tactic.data_synth] "comp subgoal hg: {hg}"
    trace[Meta.Tactic.data_synth] "comp subgoal hf: {hf}"
    let some ggoal ← isDataSynthGoal? hg | return none
    let some fgoal ← isDataSynthGoal? hf | return none
    return .some (thm, fgoal, ggoal)
  -- return none


/-- Given result for `f` and `g` return result for `f∘g` -/
def compResults (fgGoal : Goal) (thm : LambdaTheorem) (f g : Expr) (hf hg : Result) : DataSynthM (Option Result) := do
  withProfileTrace "compResults" do
    let (hintPre, hintPost) ← thm.getHint #[g,f,hg.proof,hf.proof]
    fgGoal.tryTheorem? thm.toTheorem hintPre hintPost


/-- Given goal for composition `fun x => let y:=g x; f y x` and given `f` and `g` return corresponding goals for `↿f` and `g` -/
def letGoals (thm : LambdaTheorem) (fgGoal : Goal) (f g  : Expr) : DataSynthM (Option (Goal×Goal)) := do
  withProfileTrace "letGoals" do
  let .letE gId fId hgId hfId := thm.data | throwError m!"invalid let theorem {thm.thmName}"

  let (xs, _, statement) ← forallMetaTelescope (← inferType (← mkConstWithFreshMVarLevels thm.thmName))

  try
    withMainTrace (fun _ => return m!"assigning data") do
    xs[gId]!.mvarId!.assignIfDefEq g
  catch _e =>
    trace[Meta.Tactic.data_synth] "failed assigning `{g} : {← inferType g}`  to `{xs[gId]!} :{← inferType xs[gId]!}`"
    trace[Meta.Tactic.data_synth] "{_e.toMessageData}"

    throwError s!"data_synth bug"

  try
    withMainTrace (fun _ => return m!"assigning data") do
    xs[fId]!.mvarId!.assignIfDefEq f
  catch _e =>
    trace[Meta.Tactic.data_synth] "failed assigning {f} to {xs[fId]!} of type {← inferType xs[fId]!}"
    throwError s!"data_synth bug"

  let (_,rhs) ← fgGoal.mkFreshProofGoal
  if ¬(← isDefEq statement rhs) then
    trace[Meta.Tactic.data_synth] "failed to unify {← ppExpr statement} =?= {← ppExpr rhs}"
    return none

  -- synthesize any possbile class, there might be `outParam` that nees to be filled by those
  -- classes
  for x in xs do
    if ¬(← x.mvarId!.isAssigned) then
      if let some _ ← isClass? (← inferType x) then
        try
          x.mvarId!.inferInstance
        catch _ =>
          pure ()

  let hg ← inferType xs[hgId]! >>= instantiateMVars
  let hf ← inferType xs[hfId]! >>= instantiateMVars
  let some ggoal ← isDataSynthGoal? hg
    | trace[Meta.Tactic.data_synth] "not data_synth goal {hg}"
      return none
  let some fgoal ← isDataSynthGoal? hf
    | trace[Meta.Tactic.data_synth] "not data_synth goal {hf}"
      return none
  return (fgoal, ggoal)


/-- Given result for `↿f` and `g` return result for `fun x => let y:=g x; f y x` -/
def letResults (fgGoal : Goal) (thm : LambdaTheorem) (f g : Expr) (hf hg : Result) : DataSynthM (Option Result) := do
  withProfileTrace "letResults" do
    let (hintPre,hintPost) ← thm.getHint #[g,f,hg.proof,hf.proof]
    fgGoal.tryTheorem? thm.toTheorem hintPre hintPost

/-- Given goal for composition `fun x => let y:=g x; f y x` and given `f` and `g` return corresponding goal for `(f y ·)` -/
def letSkipGoals (thm : LambdaTheorem) (fgGoal : Goal) (f g  : Expr) (y : Expr) : DataSynthM (Option Goal) := do
  withProfileTrace "letSkipGoals" do
  let .letSkip gId fId hfId := thm.data | throwError m!"invalid let theorem {thm.thmName}"

  let (xs, _, statement) ← forallMetaTelescope (← inferType (← mkConstWithFreshMVarLevels thm.thmName))

  try
    withMainTrace (fun _ => return m!"assigning data") do
    xs[gId]!.mvarId!.assignIfDefEq g
  catch _e =>
    trace[Meta.Tactic.data_synth] "failed assigning `{g} : {← inferType g}`  to `{xs[gId]!} :{← inferType xs[gId]!}`"
    trace[Meta.Tactic.data_synth] "{_e.toMessageData}"

    throwError s!"data_synth bug"

  try
    withMainTrace (fun _ => return m!"assigning data") do
    xs[fId]!.mvarId!.assignIfDefEq f
  catch _e =>
    trace[Meta.Tactic.data_synth] "failed assigning {f} to {xs[fId]!} of type {← inferType xs[fId]!}"
    throwError s!"data_synth bug"

  let (_,rhs) ← fgGoal.mkFreshProofGoal
  if ¬(← isDefEq statement rhs) then
    trace[Meta.Tactic.data_synth] "failed to unify {← ppExpr statement} =?= {← ppExpr rhs}"
    return none

  -- synthesize any possbile class, there might be `outParam` that nees to be filled by those
  -- classes
  for x in xs do
    if ¬(← x.mvarId!.isAssigned) then
      if let some _ ← isClass? (← inferType x) then
        try
          x.mvarId!.inferInstance
        catch _ =>
          pure ()

  let hf ← inferType xs[hfId]! >>= instantiateMVars
  let .forallE _ _ hf _ := hf | throwError "expected forall {← ppExpr hf}"
  let hf := hf.instantiate1 y
  let some fgoal ← isDataSynthGoal? hf | return none
  return fgoal

/-- Given result for `(f y ·)` return result for `fun x => let y:=g x; f y x` -/
def letSkipResults (fgGoal : Goal) (thm : LambdaTheorem) (f g y : Expr) (hfy : Result) : DataSynthM (Option Result) := do
  withProfileTrace "letSkipResults" do
    let (hintPre,hintPost) ← thm.getHint #[g,f, (← mkLambdaFVars #[y] hfy.proof)]
    fgGoal.tryTheorem? thm.toTheorem hintPre hintPost

set_option linter.unusedVariables false in
/-- Given goal for `fun x i => f x i` return goal for `fun x => f x i` -/
def piGoal (fGoal : Goal) (f : Expr) (i : Expr) : DataSynthM (Option (LambdaTheorem×Goal)) :=
  withProfileTrace "piGoals" do

  let thms ← getLambdaTheorems fGoal.dataSynthDecl.name .pi
  for thm in thms do
    let .pi fId hfId := thm.data | throwError m!"invalid pi theorem {thm.thmName}"

    let (xs, _, statement) ← forallMetaTelescope (← inferType (← mkConstWithFreshMVarLevels thm.thmName))

    try
      withMainTrace (fun _ => return m!"assigning data") do
      xs[fId]!.mvarId!.assignIfDefEq f
    catch _e =>
      throwError s!"{← ppExpr (xs[fId]!)} : {← ppExpr (← inferType xs[fId]!)} := {← ppExpr f}"

    let (_,rhs) ← fGoal.mkFreshProofGoal
    if ¬(← isDefEq statement rhs) then
      trace[Meta.Tactic.data_synth] "failed to unify {← ppExpr statement} =?= {← ppExpr rhs}"
      return none

    -- synthesize any possbile class, there might be `outParam` that nees to be filled by those
    -- classes
    for x in xs do
      if ¬(← x.mvarId!.isAssigned) then
        if let some _ ← isClass? (← inferType x) then
          try
            x.mvarId!.inferInstance
          catch _ =>
            pure ()

    let hf ← inferType xs[hfId]! >>= instantiateMVars
    let .forallE _ _ hf _ := hf | throwError "expected forall {← ppExpr hf}"
    let hf := hf.instantiate1 i
    let some fgoal ← isDataSynthGoal? hf | return none
    return (thm,fgoal)
  return none

set_option linter.unusedVariables false in
/-- Given result for `(f · i)` and free variable `i` return result for `f`-/
def piResult (fGoal : Goal) (thm : LambdaTheorem) (f : Expr) (i : Expr) (hfi : Result) :
    DataSynthM (Option Result) :=
  withProfileTrace "piResults" do
    let (hintPre,hintPost) ← thm.getHint #[f,(← mkLambdaFVars #[i] hfi.proof)]
    fGoal.tryTheorem? thm.toTheorem hintPre hintPost

def projGoals (thm : LambdaTheorem) (fGoal : Goal) (f g p₁ p₂ q : Expr) : DataSynthM (Option (LambdaTheorem×Goal)) := do
  withProfileTrace "projGoals" do

  let .proj fId gId p₁Id p₂Id qId hgId := thm.data
    | throwError m!"invalid proj theorem {thm.thmName}"

  let (xs, _, statement) ← forallMetaTelescope (← inferType (← mkConstWithFreshMVarLevels thm.thmName))

  try
    xs[fId]!.mvarId!.assignIfDefEq f
    xs[gId]!.mvarId!.assignIfDefEq g
    xs[p₁Id]!.mvarId!.assignIfDefEq p₁
    xs[p₂Id]!.mvarId!.assignIfDefEq p₂
    xs[qId]!.mvarId!.assignIfDefEq q
  catch e =>
    trace[Meta.Tactic.data_synth] s!"failed assigning projection data"
    trace[Meta.Tactic.data_synth] e.toMessageData
    pure ()


  let (_,rhs) ← fGoal.mkFreshProofGoal
  if ¬(← isDefEq statement rhs) then
    return none

  -- synthesize any possbile class, there might be `outParam` that nees to be filled by those
  -- classes
  for x in xs do
    if ¬(← x.mvarId!.isAssigned) then
      if let some _ ← isClass? (← inferType x) then
        try
          x.mvarId!.inferInstance
        catch _ =>
          pure ()

  let hg ← inferType xs[hgId]! >>= instantiateMVars
  let some ggoal ← isDataSynthGoal? hg | return none
  return some (thm,ggoal)

/-- Given result for `↿f` and `g` return result for `fun x => let y:=g x; f y x` -/
def projResults (fGoal : Goal) (thm : LambdaTheorem) (f g p₁ p₂ q : Expr) (hg : Result) : DataSynthM (Option Result) := do
  withProfileTrace "projResults" do
    let (hintPre, hintPost) ← thm.getHint #[f,g,p₁,p₂,q,hg.proof]
    fGoal.tryTheorem? thm.toTheorem hintPre hintPost


def constCase? (goal : Goal) (f : FunData) : DataSynthM (Option Result) := do

  -- todo: this work of checking free variables should be shared with `decomposeDomain?`
  --       Maybe `FunData` should carry a `FVarSet`
  let vars := (← f.body.collectFVars |>.run {}).2.fvarSet
  let (xs₁, _) := f.xs.partition (fun x => vars.contains x.fvarId!)

  unless xs₁.size = 0 do return none
  withProfileTrace "const case" do
  withMainTrace (fun _ => return "constant function") do

  let thms ← getLambdaTheorems goal.dataSynthDecl.name .const

  for thm in thms do
    if let some r ← goal.tryTheorem? thm.toTheorem then
      return r

  return none


def decomposeDomain? (goal : Goal) (f : FunData) : DataSynthM (Option Result) := do
  if ¬(← read).config.domainDec then
    return none
  let some (p₁,p₂,q,g) ← f.decomposeDomain? | return none
  withProfileTrace "decomposeDomain" do
  withMainTrace (fun r => pure m!"[{ExceptToEmoji.toEmoji r}] domain projection {p₁}") do

  let thms ← getLambdaTheorems goal.dataSynthDecl.name .proj
  for thm in thms do
    try
      let some (thm,ggoal) ← projGoals thm goal (← f.toExpr) (← g.toExpr) p₁ p₂ q | continue
      let some hg ← dataSynthFun ggoal g | continue
      let some r ← projResults goal thm (← f.toExpr) (← g.toExpr) p₁ p₂ q hg | continue
      let r ← r.normalize
      return r
    catch _ =>
      continue
  return none


def compCase (goal : Goal) (f g : FunData) : DataSynthM (Option Result) := do
  withProfileTrace "comp case" do
  let thms ← getLambdaTheorems goal.dataSynthDecl.name .comp
  for thm in thms do
    try
      let some (thm, fgoal, ggoal) ← compGoals thm goal (← f.toExpr) (← g.toExpr) | continue
      let some hf ← dataSynthFun fgoal f | continue
      let some hg ← dataSynthFun ggoal g | continue
      let some r ← compResults goal thm (← f.toExpr) (← g.toExpr) hf hg | continue
      let r ← r.normalize
      return r
    catch e =>
      trace[Meta.Tactic.data_synth] e.toMessageData
      continue
  return none


def letCase (goal : Goal) (f g : FunData) : DataSynthM (Option Result) := do
  withProfileTrace "letCase" do
  let fExpr ← f.toExprCurry1
  let gExpr ← g.toExpr

  -- normal let theorems
  let thms ← getLambdaTheorems goal.dataSynthDecl.name .letE
  trace[Meta.Tactic.data_synth] "let theorems: {thms.map (fun t => t.thmName)}"
  for thm in thms do
    let .letE gId fId hgId hfId := thm.data | continue
    try
      trace[Meta.Tactic.data_synth] "trying let theorem {thm.thmName}"
      let some (fgoal, ggoal) ← letGoals thm goal fExpr gExpr | continue
      -- let some hf ←
      --   withProfileTrace "solving f" do
      --   dataSynthFun fgoal f | continue
      -- let some hg ←
      --   withProfileTrace "solving g" do
      --   dataSynthFun ggoal g | continue
      -- let some r ← letResults goal thm fExpr gExpr hf hg | continue

      let hintPost : DataSynthM (Option (Array (ℕ×Expr))) := do
        let some hg ←
          withProfileTrace "solving g" do
          dataSynthFun ggoal g | pure none
        let some hf ←
          withProfileTrace "solving f" do
          dataSynthFun fgoal f | pure none
        pure (.some #[(hgId,hg.proof),(hfId,hf.proof)])

      let hintPre := #[(gId,gExpr),(fId,fExpr)]

      let some r ← goal.tryTheorem?' thm.toTheorem hintPre hintPost | continue
      let r ← r.normalize
      return r
    catch e =>
      trace[Meta.Tactic.data_synth] "trying let theorem {thm.thmName} failed badly\n{e.toMessageData}"

  -- let theorems that skip the let binding
  let thms ← getLambdaTheorems goal.dataSynthDecl.name .letSkip
  trace[Meta.Tactic.data_synth] "let theorems: {thms.map (fun t => t.thmName)}"

  f.lambdaTelescope1 fun y fy => do
  for thm in thms do
    try
      trace[Meta.Tactic.data_synth] "trying let theorem {thm.thmName}"
      let some fygoal ← letSkipGoals thm goal fExpr gExpr y | continue
      let some hfy ←
        withProfileTrace "solving f" do
        dataSynthFun fygoal fy | continue

      let some r ← letSkipResults goal thm fExpr gExpr y hfy | continue
      let r ← r.normalize
      return r
    catch e =>
      trace[Meta.Tactic.data_synth] "trying let theorem {thm.thmName} failed badly\n{e.toMessageData}"

  return none


def lamCase (goal : Goal) (f : FunData) : DataSynthM (Option Result) := do
  withProfileTrace "lamCase" do
  let fExpr ← f.toExpr
  f.bodyLambdaTelescope1 fun i fi => do
    let some (thm,figoal) ← piGoal goal fExpr i | return none
    let some hfi ← dataSynthFun figoal fi | return none
    let some r ← piResult goal thm fExpr i hfi | return none
    let r ← r.normalize
    return r


/-- Similar to `dataSynth` but driven by function. -/
partial def mainFun (goal : Goal) (f : FunData) : DataSynthM (Option Result) := do
  withIncRecDepth do
  withProfileTrace "mainFun" do

  -- spacial case for constant functions
  if let some r ← constCase? goal f then
    return r

  -- decompose domain if possible
  if let some r ← decomposeDomain? goal f then
    return r

  trace[Meta.Tactic.data_synth] "main function {←f.pp}"

  let h ← f.funHead
  trace[Meta.Tactic.data_synth] "function case {repr h}"

  match h with
  | .app  | .fvar _ | .bvar _ =>
    if let .some r ← mainCached goal (initialTrace:=false) then
      return r
    else if let .some (f,g) ← f.nontrivialAppDecomposition then
      trace[Meta.Tactic.data_synth] "decomposition {← f.toExpr} ∘ {← g.toExpr}"
      compCase goal f g
    else
      return none
  | .letE =>
    match ← f.getBodyLetCase with
    | .comp f g => compCase goal f g
    | .letE f g => letCase goal f g
    | .simple f => dataSynthFun goal f
  | .lam => lamCase goal f
  | _ => return none


def mainFunCached (goal : Goal) (f : FunData) : DataSynthM (Option Result) := do

  withMainTrace
    (fun r =>
      match r with
      | .ok (some _r) => return m!"[✅] {← goal.pp}"
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
