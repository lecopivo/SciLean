import Lean
import Lean.Util.Trace

import Aesop

import SciLean.Lean.Meta.Basic

import SciLean.Tactic.GTrans.MetaLCtxM

import SciLean.Tactic.FunTrans.Core
import SciLean.Tactic.FunTrans.Elab

open Lean Meta


namespace SciLean.Tactic.LSimp


----------------------------------------------------------------------------------------------------
-- Result ------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

structure Result where
  expr : Expr
  proof? : Option Expr := none
  vars : Array Expr := #[]
  cache          : Bool := true
  deriving Inhabited


def mkEqTransOptProofResult (h? : Option Expr) (cache : Bool) (r : Result) : MetaM Result :=
  match h?, cache with
  | none, true  => return r
  | none, false => return { r with cache := false }
  | some p₁, cache => match r.proof? with
    | none    => return { r with proof? := some p₁, cache := cache && r.cache }
    | some p₂ => return { r with proof? := (← Meta.mkEqTrans p₁ p₂), cache := cache && r.cache }

def Result.mkEqTrans (r₁ r₂ : Result) : MetaM Result :=
  mkEqTransOptProofResult r₁.proof? r₁.cache {r₂ with vars := r₁.vars ++ r₂.vars}

def _root_.Lean.Meta.Simp.Result.toLResult (s : Simp.Result) : Result :=
  { expr := s.expr,
    proof? := s.proof?,
    vars := #[],
    cache := s.cache }

def Result.getProof (r : Result) : MetaM Expr :=
  match r.proof? with
  | some p => return p
  | none   => mkEqRefl r.expr

def mkCongrFun (r : Result) (a : Expr) : MetaM Result :=
  match r.proof? with
  | none   => return { expr := mkApp r.expr a, proof? := none, vars := r.vars }
  | some h => return { expr := mkApp r.expr a, proof? := (← Meta.mkCongrFun h a), vars := r.vars }

def mkCongr (r₁ r₂ : Result) : MetaM Result :=
  let e := mkApp r₁.expr r₂.expr
  match r₁.proof?, r₂.proof? with
  | none,     none   => return { expr := e, proof? := none, vars := r₁.vars ++ r₂.vars }
  | some h,  none    => return { expr := e, proof? := (← Meta.mkCongrFun h r₂.expr), vars := r₁.vars ++ r₂.vars }
  | none,    some h  => return { expr := e, proof? := (← Meta.mkCongrArg r₁.expr h), vars := r₁.vars ++ r₂.vars }
  | some h₁, some h₂ => return { expr := e, proof? := (← Meta.mkCongr h₁ h₂), vars := r₁.vars ++ r₂.vars }

def mkImpCongr (src : Expr) (r₁ r₂ : Result) : MetaLCtxM Result := do
  let e := src.updateForallE! r₁.expr r₂.expr
  match r₁.proof?, r₂.proof? with
  | none,     none   => return { expr := e, proof? := none, vars := r₁.vars ++ r₂.vars }
  | _,        _      => return { expr := e, proof? := (← Meta.mkImpCongr (← r₁.getProof) (← r₂.getProof)), vars := r₁.vars ++ r₂.vars } -- TODO specialize if bottleneck


/-- Binds all variables to the result expression and proof. Useful when returning result to a context
where `r.vars` are no longer valid.

This is useful when running `MetaLCtxM.runInMeta` or `LSimpM.runInMeta` and you want make the
result valid in the original context. E.g. `(lsimp x).runInMeta (fun r => r.binVars)`   -/
def Result.bindVars (r : Result) : MetaM Result := do
  return { r with expr := ← mkLambdaFVars r.vars r.expr
                  proof? := ← r.proof?.mapM (fun h => mkLambdaFVars r.vars h)
                  vars := #[] }

----------------------------------------------------------------------------------------------------
-- LSimpM ------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

abbrev Cache := ExprMap Result

structure State where
  /-- Cache storing lsimp results. -/
  cache : IO.Ref Cache
  simpState : IO.Ref Simp.State
  timings : Batteries.RBMap String Aesop.Nanos compare := {}

abbrev LSimpM := ReaderT Simp.Methods $ ReaderT Simp.Context $ StateT State MetaLCtxM

instance : MonadLift SimpM LSimpM where
  monadLift x := fun m c s => do return (← x m.toMethodsRef c s.simpState, s)

/-- Run `x : LSimpM X` without modifying the local context.

This effectively runs `x : LSimpM X`, modifies the local context and then reverts the context back.
The function `k` is evaluated on the result of `x` in the modified context before the context is
reverted back. It is user's responsibility to make sure that the `k` modifies the result such
that it is valid in the original context e.g. bind all newly introduced free variables. -/
def LSimpM.runInMeta (x : LSimpM X) (k : X → MetaM Y) : LSimpM Y := do
  fun mths ctx s => do
    -- let m : Simp.Methods := Simp.MethodsRef.toMethods mths.toMethodsRef
    let (r,s') ← (x mths ctx s).runInMeta (fun (x,s') => do pure (← k x, s'))
    return (r,s')

instance : Inhabited (LSimpM α) where
  default := fun _ _ _ _ _ _ => default

def timeThis (key : String) (x : LSimpM α) : LSimpM α := do
  let (a, t) ← Aesop.time x
  modifyThe State fun s => {s with timings := s.timings.alter key (fun t' => .some (t'.getD 0 + t))}
  return a

def _root_.Aesop.Nanos.print (n : Aesop.Nanos) : String :=
  if n.nanos < 1000 then
    s!"{n.nanos}ns"
  else if n.nanos < 1000000 then
    let str := toString (n.nanos.toFloat / 1000)
    match str.split λ c => c == '.' with
    | [beforePoint] => beforePoint ++ "μs"
    | [beforePoint, afterPoint] => beforePoint ++ "." ++ afterPoint.take 1 ++ "μs"
    | _ => unreachable!
  else
    let str := toString (n.nanos.toFloat / 1000000)
    match str.split λ c => c == '.' with
    | [beforePoint] => beforePoint ++ "ms"
    | [beforePoint, afterPoint] => beforePoint ++ "." ++ afterPoint.take 1 ++ "ms"
    | _ => unreachable!


def State.printTimings (s : State) : MetaM Unit := do
  let t := s.timings
  for (k,t) in t do
    trace[Meta.Tactic.simp.time] "{k} took {t.print}"


----------------------------------------------------------------------------------------------------
-- LSimp forward declaration -----------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[extern "scilean_lsimp"]
opaque lsimp (e : Expr) : LSimpM Result

@[extern "scilean_ldsimp"]
opaque ldsimp (e : Expr) : LSimpM Expr


----------------------------------------------------------------------------------------------------
-- Step --------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

inductive Step where
  | done (r : Result)
  | visit (e : Result)
  | continue (e? : Option Result := none)
  deriving Inhabited

def mkEqTransResultStep (r : Result) (s : Step) : MetaM Step :=
  match s with
  | .done r'            => return .done (← mkEqTransOptProofResult r.proof? r.cache r')
  | .visit r'           => return .visit (← mkEqTransOptProofResult r.proof? r.cache r')
  | .continue none      => return .continue r
  | .continue (some r') => return .continue (some (← mkEqTransOptProofResult r.proof? r.cache r'))

def _root_.Lean.Meta.Simp.Step.toLStep (s : Simp.Step) : Step :=
  match s with
  | .done r => LSimp.Step.done r.toLResult
  | .visit r => LSimp.Step.visit r.toLResult
  | .continue r => LSimp.Step.continue (r.map (·.toLResult))


----------------------------------------------------------------------------------------------------
-- Utility Functions -------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

def pre (e : Expr) : LSimpM Step := do
  timeThis "pre" <|
    (Simp.getMethods >>= (·.pre e) >>= fun s => pure s.toLStep)

def post (e : Expr) : LSimpM Step := do
  timeThis "post" <|
    (Simp.getMethods >>= (·.post e) >>= fun s => pure s.toLStep)


@[inline] def getContext : LSimpM Simp.Context :=
  readThe Simp.Context

def getConfig : LSimpM Simp.Config :=
  return (← getContext).config

@[inline] def withParent (parent : Expr) (f : LSimpM α) : LSimpM α :=
  withTheReader Simp.Context (fun ctx => { ctx with parent? := parent }) f

@[inline] def withSimpTheorems (s : SimpTheoremsArray) (x : LSimpM α) : LSimpM α := do
  savingCache <| withTheReader Simp.Context (fun ctx => { ctx with simpTheorems := s }) x
