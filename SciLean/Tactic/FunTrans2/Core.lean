import Lean
import Lean.Util.Trace

import SciLean.Lean.Meta.Basic

import SciLean.Tactic.FunTrans.Core

open Lean Meta

initialize registerTraceClass `Meta.Tactic.fun_trans2
initialize registerTraceClass `Meta.Tactic.fun_trans2.fun_trans
initialize registerTraceClass `Meta.Tactic.fun_trans2.quick
initialize registerTraceClass `Meta.Tactic.fun_trans2.normalize

-- /-- Transforms `e` into `e'` where `e'` and calls `k xs e' h` where `xs` are new free variables
-- appearing in `e'` and `h` is proof of `e = mkLambdaFVars xs e'`. -/
-- partial def funTrans2 (e : Expr) (k : Array Expr → Expr → Expr → MetaM α) : MetaM α := do

--   withTraceNode `Meta.Tactic.fun_trans2 (fun r => do pure s!"{← ppExpr e}") do

--   match e with
--   | .app .. =>
--     e.withApp fun fn xs => do
--       funTrans2 fn fun fxs fn' h => do
--         funTrans2Rec xs.toList #[] #[] #[] fun xxs xs' hx => do
--           k (fxs++xxs) (fn'.beta xs') default

--     -- funTrans2 f fun fxs fb fh => do

--     --   if ¬(← isType x) then
--     --     funTrans2 x fun xxs xb xh => do
--     --       k (fxs ++ xxs) (fb.app xb) default -- todo: fix proof
--     --   else
--     --     k fxs (fb.app x) default -- todo: fix proof
--   | .letE n t v b _ =>
--     -- todo: check for dependent let and do something else
--     Meta.withLetDecl n t v fun y => do
--       funTrans2 v fun ys v' h => do
--         Meta.withLetDecl n t v' fun y' => do
--           let b' := b.instantiate1 y'
--           k (ys.push y') b' default -- todo: fix proof
--   | _ =>
--     k #[] e default -- todo: fix proof
-- where
--   funTrans2Rec (es : List Expr) (xs es' hs : Array Expr) (k : Array Expr → Array Expr → Array Expr → MetaM α) : MetaM α := do
--     match es with
--     | [] => k xs es' hs
--     | e :: es =>
--       funTrans2 e fun xs'' e'' h'' => do
--         funTrans2Rec es (xs ++ xs'') (es'.push e'') (hs.push h'') k

structure Result where
  val : Expr
  vars : Array Expr
  proof : Expr
  lctx : LocalContext
  insts : LocalInstances


def Result.withCtx (r : Result) (m : MetaM α) : MetaM α :=
  withLCtx r.lctx r.insts m

def Result.toExpr (r : Result) : MetaM Expr :=
  r.withCtx do mkLambdaFVars r.vars r.val

def mkLetBinding (e : Expr) : MetaM Bool :=
  if e.isFVar ||
     e.isAppOfArity ``OfNat.ofNat 3 ||
     e.isAppOfArity ``OfScientific.ofScientific 5 ||
     e.isLambda then
    return false
  else
    return true


private def skip (e : Expr) : MetaM Bool := do
  let E ← inferType e
  -- skip types
  if ← isType e then
    return true

  -- skip instances
  if (← isClass? E).isSome then
    return true

  return false


def letAppNormalize (e : Expr) : MetaM Expr := do
  e.withApp fun fn xs => do
    letTelescope fn fun ys fn' => do
      mkLambdaFVars ys (fn'.beta xs)


partial def projNormalize (e : Expr) : MetaM Expr := do
  if e.isAppOf ``Prod.fst ||
     e.isAppOf ``Prod.snd then
     let n := e.getAppNumArgs
     match compare n 3 with
     | .lt => return e
     | .eq =>
       if e.isAppOfArity ``Prod.fst 3 &&
         e.appArg!.isAppOfArity ``Prod.mk 4 then
         projNormalize (e.appArg!.appFn!.appArg!)
       else if e.isAppOfArity ``Prod.snd 3 &&
         e.appArg!.isAppOfArity ``Prod.mk 4 then
         projNormalize (e.appArg!.appArg!)
       else
         return e
     | .gt =>
       return (← projNormalize e.appFn!).app e.appArg!
  else
    return e

partial def projNormalize' (e : Expr) : Option Expr := do
  if e.isAppOf ``Prod.fst ||
     e.isAppOf ``Prod.snd then
     let n := e.getAppNumArgs
     match compare n 3 with
     | .lt => .none
     | .eq =>
       if e.isAppOfArity ``Prod.fst 3 &&
         e.appArg!.isAppOfArity ``Prod.mk 4 then
         let val := (e.appArg!.appFn!.appArg!)
         (projNormalize' val).getD val
       else if e.isAppOfArity ``Prod.snd 3 &&
         e.appArg!.isAppOfArity ``Prod.mk 4 then
         let val := (e.appArg!.appArg!)
         (projNormalize' val).getD val
       else
         .none
     | .gt =>
       (projNormalize' e.appFn!).map (fun e' => e'.app e.appArg!)
  else
    .none



def projNormalizeSimple (e : Expr) : Option Expr := do
  if e.isAppOfArity ``Prod.fst 3 &&
     e.appArg!.isAppOfArity ``Prod.mk 4 then
     .some e.appArg!.appFn!.appArg!
  else if e.isAppOfArity ``Prod.snd 3 &&
     e.appArg!.isAppOfArity ``Prod.mk 4 then
     .some e.appArg!.appArg!
  else
    .none


def normalize'' (e : Expr) : MetaM Expr := do
  let e ← letAppNormalize e   -- this reduction should be done immediately after applying simp theorem with extra arguments
  let e ← projNormalize e
  let e := e.headBeta

  -- let e ← withReducibleAndInstances <| whnfCore e {zeta:=false, proj:=.no}
  return e


partial def normalizeLetValue (lctx : LocalContext) (insts : LocalInstances) (n : Name) (t e : Expr) :
    MetaM Result := do

  withLCtx lctx insts do
    if ¬(← mkLetBinding e) then
      return ⟨e, #[], default, lctx, insts⟩
    else
      if e.isAppOfArity ``Prod.mk 4 then
        let e₁ := e.appFn!.appArg!
        let e₂ := e.appArg!
        let r₁ ← normalizeLetValue lctx insts (n.appendAfter "₁") t e₁
        let r₂ ← normalizeLetValue r₁.lctx r₁.insts (n.appendAfter "₂") t e₂
        r₂.withCtx do
          return ⟨← mkAppM ``Prod.mk #[r₁.val, r₂.val], r₁.vars ++ r₂.vars, default, r₂.lctx, r₂.insts⟩
      else
        withLetDecl n t e fun x => do
          return ⟨x, #[x], default, ← getLCtx, ← getLocalInstances⟩

/-- Transforms `e` into `e'` where `e'` and calls `k xs e' h` where `xs` are new free variables
appearing in `e'` and `h` is proof of `e = mkLambdaFVars xs e'`. -/
partial def funTrans2
    (lctx : LocalContext) (insts : LocalInstances)
    (e : Expr) : SimpM Result := do

  withLCtx lctx insts do

  withTraceNode `Meta.Tactic.fun_trans2 (fun r => do match r with | .ok r => pure s!"{← ppExpr e}\n==>\n{← ppExpr (← r.toExpr)}" | _ => pure "bum" ) do

  withTraceNode `Meta.Tactic.fun_trans2.quick (fun r => do pure "" ) do

  modify fun s => { s with numSteps := s.numSteps + 1}

  let e ← normalize'' e

  let s ←
    withTraceNode `Meta.Tactic.fun_trans2.fun_trans (fun r => do pure "") do
      Mathlib.Meta.FunTrans.funTrans e
     -- (Simp.mkDefaultMethodsCore #[]).toMethodsRef {config:={zeta:=false}} (← IO.mkRef {})

  let e :=
    match s with
    | .done r => r.expr
    | .visit r => r.expr
    | .continue (.some r) => r.expr
    | .continue none => e

  -- trace[Meta.Tactic.fun_trans2] "ftrans to {← ppExpr e}"

  let e ← normalize'' e

  -- trace[Meta.Tactic.fun_trans2] "normalized to {← ppExpr e}"


  match e with
  | .app .. =>
    e.withApp fun fn xs => do
      let mut lctx := lctx
      let mut insts := insts
      let ⟨fn',fxs,hf,lctx',insts'⟩ ← funTrans2 lctx insts fn
      lctx := lctx'
      insts := insts'

      let mut xxs : Array Expr := #[]
      let mut xs' : Array Expr := #[]
      for x in xs do
        if ← skip x then
          xs' := xs'.push x
          continue
        else
          let ⟨x', xxs', hx, lctx',insts'⟩ ← funTrans2 lctx insts x
          lctx := lctx'
          insts := insts'
          xs' := xs'.push x'
          xxs := xxs ++ xxs'
      let vars := fxs++xxs
      -- trace[Meta.Tactic.fun_trans2] "app vars {← vars.mapM ppExpr}"

      let val' ← normalize'' (fn'.beta xs')

      withLCtx lctx insts do
        letTelescope val' fun xs'' val'' => do
          let r : Result := ⟨val'', fxs++xxs++xs'', default, ← getLCtx, ← getLocalInstances⟩
          trace[Meta.Tactic.fun_trans2] "result {← ppExpr (← r.toExpr)}"
          return r

  | .letE n t v b _ =>

    let rv ← funTrans2 lctx insts v

    -- trace[Meta.Tactic.fun_trans2] "normalizing let value {← ppExpr (← rv.toExpr)}"
    let rv' ← normalizeLetValue rv.lctx rv.insts n t rv.val
    -- trace[Meta.Tactic.fun_trans2] "normalized to {← ppExpr (← rv'.toExpr)}"


    let b' ←
      rv'.withCtx do Meta.transform (b.instantiate1 rv'.val) (post := fun e => match projNormalize' e with | .some e' => return .done e' | .none => return .continue)


    -- rv'.withCtx do
    --   trace[Meta.Tactic.fun_trans2] "hihi\n{← ppExpr e}"
    --   trace[Meta.Tactic.fun_trans2] "hoho\n{← ppExpr b'}"

    let rb ← funTrans2 rv'.lctx rv'.insts b' -- (b.instantiate1 rv'.val)

    if rb.val.isLet then
      throwError "problem {← ppExpr e}"


    let r : Result := ⟨rb.val, rv.vars ++ rv'.vars ++ rb.vars, default, rb.lctx, rb.insts⟩
    return r

  | .lam n t b bi =>
    withLocalDecl n bi t fun var => do
      let rb ← funTrans2 (← getLCtx) (← getLocalInstances) (b.instantiate1 var)

      let r : Result := ⟨← mkLambdaFVars #[var] (← rb.toExpr), #[], default, lctx, insts⟩
      return r

  | _ =>
    return ⟨e, #[], default, lctx, insts⟩



def callFunTrans2 (e : Expr) : MetaM Result := do

  let stateRef : IO.Ref Simp.State ← IO.mkRef {}
  let s ← (funTrans2 (← getLCtx) (← getLocalInstances) e).run
     (Simp.mkDefaultMethodsCore #[]).toMethodsRef {config:={zeta:=false},simpTheorems:=#[←getSimpTheorems]} stateRef

  let state ← stateRef.get
  IO.println s!"fun_trans2 took {state.numSteps} steps"

  return s
