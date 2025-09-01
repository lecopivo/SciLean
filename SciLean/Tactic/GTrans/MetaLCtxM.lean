import Lean
import Qq

import SciLean.Lean.Meta.Basic

open Lean Meta

structure _root_.Lean.Meta.ContextCtx where
  lctx              : LocalContext         := {}
  localInstances    : LocalInstances       := #[]
  deriving Inhabited

open private Lean.Meta.Config.toKey from Lean.Meta.Basic in
structure _root_.Lean.Meta.ContextCfg where
  config            : Meta.Config          := {}
  configKey         : UInt64               := config.toKey
  defEqCtx?         : Option DefEqContext  := none
  synthPendingDepth : Nat                  := 0
  canUnfold?        : Option (Meta.Config → ConstantInfo → CoreM Bool) := none
  univApprox        : Bool := false
  inTypeClassResolution : Bool := false


def Lean.Meta.Context.toCtx (ctx : Meta.Context) : ContextCtx where
  lctx := ctx.lctx
  localInstances := ctx.localInstances

open Meta.Context in
open private Meta.Context.config from Lean.Meta.Basic in -- this does not work :( se we have to to it with Meta.getConfig and throught CoreM
def _root_.Lean.Meta.Context.getConfig (ctx : Meta.Context) : CoreM Meta.Config := do
  let a : MetaM Meta.Config := Meta.getConfig
  let (c,_) ← a.run ctx {}
  pure c

def Lean.Meta.Context.toCfg (ctx : Meta.Context) : CoreM ContextCfg := do return {
  config := ← ctx.getConfig
  defEqCtx? := ctx.defEqCtx?
  synthPendingDepth := ctx.synthPendingDepth
  canUnfold? := ctx.canUnfold?
  univApprox := ctx.univApprox
  inTypeClassResolution := ctx.inTypeClassResolution
}


def _root_.Lean.Meta.Context.mkCtxCfg (ctx : ContextCtx) (cfg : ContextCfg) : Meta.Context :=
  { config := cfg.config
    lctx := ctx.lctx
    localInstances := ctx.localInstances
    defEqCtx? := cfg.defEqCtx?
    synthPendingDepth := cfg.synthPendingDepth
    canUnfold? := cfg.canUnfold? }

-- TODO: change the monad such that we can only add variables to the context and not remove them
--       or completely changes the context
/-- Similar to `MetaM` but allows modifying local context.

Most imporantly it has a variant of `lambdaTelescope` called `introLet` such that instead of
```
lambdaTelescope e fun xs b => do
  f xs b
```
we can call
```
let (b,xs) ← lambdaIntro e
f xs b
```

For example running `lambdaTelescope` does not work well with for loops but `lambdaIntro` does.

Important functions introducing new free variables to the context:
  - `lambdaIntro`
  - `letIntro`
  - `introLocalDecl`
  - `introLetDecl`

Also you can run `MetaLCtxM` inside of `MetaM` with `MetaLCtxM.runInMeta`.
 -/
abbrev MetaLCtxM  := ReaderT Meta.ContextCfg $ StateT Meta.ContextCtx $ StateRefT Meta.State CoreM


@[always_inline]
instance : Monad MetaLCtxM := let i := inferInstanceAs (Monad MetaLCtxM); { pure := i.pure, bind := i.bind }

instance {α} [Inhabited α] : Inhabited (MetaLCtxM α) where
  default := fun _ ctx => do pure (default,ctx)

instance : MonadLCtx MetaLCtxM where
  getLCtx := return (← get).lctx

instance : MonadMCtx MetaLCtxM where
  getMCtx    := return (← getThe Meta.State).mctx
  modifyMCtx f := modifyThe Meta.State fun s => { s with mctx := f s.mctx }

instance : MonadEnv MetaLCtxM where
  getEnv      := return (← getThe Core.State).env
  modifyEnv f := do modifyThe Core.State fun s => { s with env := f s.env, cache := {} }; modifyThe Meta.State fun s => { s with cache := {} }

instance : AddMessageContext MetaLCtxM where
  addMessageContext := addMessageContextFull

instance : MonadLift MetaM MetaLCtxM where
  monadLift x := fun cfg ctx => do let r ← x (.mkCtxCfg ctx cfg); pure (r, ctx)

protected def MetaLCtxM.saveState : MetaLCtxM (SavedState×ContextCtx) :=
  return ({ core := (← Core.saveState), meta := (← get) }, ⟨← getLCtx, ← getLocalInstances⟩)

def MetaLCtxM.restore (b : SavedState) (ctx : ContextCtx) : MetaLCtxM Unit := do
  b.restore
  modify fun s => { s with mctx := b.meta.mctx, zetaDeltaFVarIds := b.meta.zetaDeltaFVarIds, postponed := b.meta.postponed }
  modifyThe ContextCtx fun _ => ctx

instance : MonadBacktrack (SavedState×ContextCtx) MetaLCtxM where
  saveState      := MetaLCtxM.saveState
  restoreState s := MetaLCtxM.restore s.1 s.2

@[inline] def MetaLCtxM.run (x : MetaLCtxM α) (cfg : ContextCfg := {}) (ctx : ContextCtx := {}) (s : Meta.State := {}) :
    CoreM (α × Meta.State) := do
  let ((r,_),s) ← x cfg ctx |>.run s
  return (r,s)

@[inline] def MetaLCtxM.run' (x : MetaLCtxM α) (cfg : ContextCfg := {}) (ctx : ContextCtx := {}) (s : Meta.State := {}) : CoreM α := do
  let ((r,_),_) ← x cfg ctx |>.run s
  return r

/-- Run `a : MetaLCtx X` without modifying the local context.

This effectively runs `a : MetaLCtx X`, modifies the local context and then reverts the context back.
The function `k` is evaluated on the result of `a` in the modified context before the context is
reverted back. It is user's responsibility to make sure that the `k` modifies the result such
that it is valid in the original context e.g. bind all newly introduced free variables. -/
@[inline] def Lean.Meta.withoutModifyingLCtx (k : α → MetaM β) (a : MetaLCtxM α) : MetaM β :=
  fun ctx => do
    let cfg ← ctx.toCfg
    let ctx' := ctx.toCtx
    let (a,ctx) ← a cfg ctx'
    k a (.mkCtxCfg ctx cfg)


/-- Run `a : MetaLCtx X` without modifying the local context.

This effectively runs `a : MetaLCtx X`, modifies the local context and then reverts the context back.
The function `k` is evaluated on the result of `a` in the modified context before the context is
reverted back. It is user's responsibility to make sure that the `k` modifies the result such
that it is valid in the original context e.g. bind all newly introduced free variables. -/
@[inline] def MetaLCtxM.runInMeta (a : MetaLCtxM α) (k : α → MetaM β) : MetaM β :=
  fun ctx => do
    let cfg ← ctx.toCfg
    let ctx' := ctx.toCtx
    let (a,ctx) ← a cfg ctx'
    k a (.mkCtxCfg ctx cfg)


instance : MonadControl MetaM MetaLCtxM where
  stM      := fun α => α × ContextCtx
  liftWith := fun f => do
    let f' := (f (fun x c s => do
                      let (x',ctx') ← x (← c.toCfg) ⟨c.lctx,c.localInstances⟩ s
                      return (x', ctx')))
    f'
  restoreM := fun x => do let (a, s) ← liftM x; set s; pure a


def lambdaIntro (e : Expr) : MetaLCtxM (Expr × Array Expr) := do
  Meta.lambdaTelescope e fun xs e' => do
    let ctx ← getThe ContextCtx
    fun _ _ => return ((e',xs), ctx)


def letIntro (e : Expr) : MetaLCtxM (Expr × Array Expr) := do
  Meta.letTelescope e fun xs e' => do
    let ctx ← getThe ContextCtx
    fun _ _ => return ((e',xs), ctx)


/-- Adds let declaration into the local context. Returns newly created free variable.

Similar to `withLetDecl` but runs in `MetaLCtxM` instead of `MetaM`. -/
def introLocalDecl (name : Name) (bi : BinderInfo) (type : Expr) : MetaLCtxM Expr := do
  let fvarId ← mkFreshFVarId
  fun _ ctx =>
    let ctx := {ctx with lctx := ctx.lctx.mkLocalDecl fvarId name type bi .default}
    let fvar := Expr.fvar fvarId
    return (fvar, ctx)


/-- Adds let declaration into the local context. Returns newly created free variable.

Similar to `withLetDecl` but runs in `MetaLCtxM` instead of `MetaM`. -/
def introLetDecl (name : Name) (type? : Option Expr) (val : Expr) : MetaLCtxM Expr := do
  let type := type?.getD (← inferType val)
  let fvarId ← mkFreshFVarId
  fun _ ctx => do
    let ctx := {ctx with lctx := ctx.lctx.mkLetDecl fvarId name type val (nonDep := false) .default}
    let fvar := Expr.fvar fvarId
    return (fvar, ctx)


-- open Lean Meta Qq in
-- #eval show MetaLCtxM Unit from do
--   let e := q(fun a b => a + b + 42)

--   let (b, xs) ← lambdaIntro e

--   IO.println s!"lambda body: {← ppExpr b}"
--   IO.println s!"lambda vars: {← liftM <| xs.mapM ppExpr}"
--   IO.println s!"lambda: {← ppExpr (← mkLambdaFVars xs b)}"
