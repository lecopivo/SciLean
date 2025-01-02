import Lean
import Lean.Util.Trace

import Aesop.Nanos
import Aesop.Util.Basic
import Batteries.Data.List.Basic

import SciLean.Lean.Meta.Basic

import SciLean.Tactic.GTrans.MetaLCtxM

import SciLean.Tactic.FunTrans.Core
import SciLean.Tactic.FunTrans.Elab

open Lean Meta


namespace SciLean.Tactic.LSimp


----------------------------------------------------------------------------------------------------
-- Result ------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


/-- Result of `lsimp` -/
structure Result where
  /-- Result of simplification  -/
  expr : Expr
  /-- Proof that the result is propositionally equal to the original expression. It is `none` if
  it is defeq to the original. -/
  proof? : Option Expr := none
  /-- This array keeps track of the newly introduced free variables that appear in the result.
  We run `lsimp` in `MetaLCtxM` which allows modifying the local context by adding new free
  variables.

  See `Result.bindVars` which is a function that takes the result and the proof and binds all
  these newly introduced free variables such that the result is valid in the original context
  of the expression we are simplifying. -/
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

/-- `lsimp`'s cache is a stack of caches. This allows us to run `lsimp` and easiliy discart all
changes to the cache by simply increasing the cache stack depth.  -/
abbrev Cache := List (ExprMap Result)

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
def withoutModifyingLCtx (k : X → MetaM Y) (x : LSimpM X) : LSimpM Y := do
  fun mths ctx s => do
    Meta.withoutModifyingLCtx (fun (x,s') => do pure (← k x, s'))
      (x mths ctx s)

-- @[deprecated]
def LSimpM.runInMeta (x : LSimpM X) (k : X → MetaM Y) : LSimpM Y := do
  fun mths ctx s => do
    -- let m : Simp.Methods := Simp.MethodsRef.toMethods mths.toMethodsRef
    let (r,s') ← Meta.withoutModifyingLCtx (fun (x,s') => do pure (← k x, s')) (x mths ctx s)
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


/-- Run `x` and discart any changes to the cache.

The cache is modified while running `x` but all changes are discarted once `x` is done.  -/
def withoutModifyingCache {α} (x : LSimpM α) : LSimpM α :=
  fun m ctx s  => do
    let cacheRef := s.cache
    -- increase stack depth
    cacheRef.modify fun c => {} :: c
    let (x',s') ← x m ctx s
    let cacheRef := s'.cache
    -- decrease stack depth
    -- todo: give an option to do custom salvage of the cache modification
    --       for example when we enter a scope with few new fvars we have to discart everything
    --       using those fvars and their dependencies but keep the rest
    cacheRef.modify fun c => c.tail
    return (x',s')


def cacheInsert (e : Expr) (r : Result) : LSimpM Unit := do
  let s ← getThe State
  s.cache.modify (fun c => c.modifyHead (fun c => c.insert e r))
  pure ()


def cacheFind? (e : Expr) : LSimpM (Option Result) := do
  let s ← getThe State
  let c ← s.cache.get
  return c.findSome? (fun c => c[e]?)


-- def traceCache : LSimpM Unit := do
--   let cache ← (← getThe State).cache.get

--   let mut s : MessageData := "lsimp cache:"
--   for c in cache, i in [0:cache.length] do
--     s := s ++ m!"\n  cache depth {i}"
--     for (e,r) in c do
--       s := s ++ m!"\n    {e} ==> {r.expr}"
--       pure ()

--   trace[Meta.Tactic.simp.cache] s



----------------------------------------------------------------------------------------------------
-- LSimp forward declaration -----------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

initialize lsimpRef  : IO.Ref (Expr → LSimpM Result) ← IO.mkRef (fun e => return {expr := e})
initialize ldsimpRef : IO.Ref (Expr → LSimpM Expr)   ← IO.mkRef (fun e => return e)

def lsimp  (e : Expr) : LSimpM Result := do (← lsimpRef.get) e
def ldsimp (e : Expr) : LSimpM Expr   := do (← ldsimpRef.get) e


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


def getContextWithParent (e : Expr) : SimpM Simp.Context := do
  Simp.withParent e (readThe Simp.Context)

open private Lean.Meta.Simp.Context.mk from Lean.Meta.Tactic.Simp.Types in -- this does not work :(
@[inline] def withParent (parent : Expr) (f : LSimpM α) : LSimpM α := do
  let ctx' ← getContextWithParent parent
  withTheReader Simp.Context (fun _ctx => ctx') f

@[inline] def withSimpTheorems (s : SimpTheoremsArray) (x : LSimpM α) : LSimpM α := do
  savingCache <| withTheReader Simp.Context (fun ctx => ctx.setSimpTheorems s) x
