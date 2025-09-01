import SciLean.Lean.Meta.Basic

namespace SciLean

open Lean Meta

inductive ReplacePost where
  | yield (e : Expr)
  | done (e : Expr)

def ReplacePost.val (r : ReplacePost) : Expr :=
  match r with
  | yield e  => e
  | done e => e

private partial def replaceFVarAndPostImpl (e : Expr) (id : FVarId) (val : Expr) (post : Expr → MetaM ReplacePost) : MetaM ReplacePost :=
  if ¬e.hasFVar then
    return .done e
  else
  match e with
  | .fvar id' =>
    if id' == id then
      return .yield val
    else
      return .done e
  | .app f x => do
    match ← replaceFVarAndPostImpl f id val post, ← replaceFVarAndPostImpl x id val post with
    | .yield f', .yield x'
    | .yield f', .done x'
    | .done f', .yield x' => post (.app f' x')
    | .done f', .done x' => return .done (.app f' x')
  | .lam n t b bi => do
    let t' ← replaceFVarAndPostImpl t id val post
    withLocalDecl n bi t'.val fun var => do
      match t', ← replaceFVarAndPostImpl (b.instantiate1 var) id val post with
      | .yield _, .yield b'
      | .yield _, .done b'
      | .done _, .yield b' => post (← mkLambdaFVars #[var] b')
      | .done _, .done b' => return .done (← mkLambdaFVars #[var] b')
  | .forallE n t b bi => do
    let t' ← replaceFVarAndPostImpl t id val post
    withLocalDecl n bi t'.val fun var => do
      match t', ← replaceFVarAndPostImpl (b.instantiate1 var) id val post with
      | .yield _, .yield b'
      | .yield _, .done b'
      | .done _, .yield b' => post (← mkForallFVars #[var] b')
      | .done _, .done b' => return .done (← mkForallFVars #[var] b')
  | .letE n t v b _ => do
    let t' ← replaceFVarAndPostImpl t id val post
    withLocalDecl n .default t'.val fun var => do
      match ← replaceFVarAndPostImpl v id val post, ← replaceFVarAndPostImpl (b.instantiate1 var) id val post with
      | .yield v', .yield b'
      | .yield v', .done b'
      | .done v', .yield b' =>
        post (.letE n (← inferType v') v' (b'.abstract #[var]) false)
      | .done v', .done b' =>
        return .done (.letE n (← inferType v') v' (b'.abstract #[var]) false)
  | .mdata _ e => replaceFVarAndPostImpl e id val post
  | .proj n i e => do
    match ← replaceFVarAndPostImpl e id val post with
    | .yield e' => post (.proj n i e')
    | .done e' => return .done (.proj n i e')
  | .mvar _ => do replaceFVarAndPostImpl (← instantiateMVars e) id val post
  | e => return .done e


private partial def instantiate1AndPostImpl (e : Expr) (i : Nat) (val : Expr) (post : Expr → MetaM ReplacePost) : MetaM ReplacePost :=
  if e.looseBVarRange < i then
    return .done e
  else
  match e with
  | .bvar i' =>
    if i' == i then
      return .yield val
    else
      return .done e
  | .app f x => do
    match ← instantiate1AndPostImpl f i val post, ← instantiate1AndPostImpl x i val post with
    | .yield f', .yield x'
    | .yield f', .done x'
    | .done f', .yield x' => post (.app f' x')
    | .done f', .done x' => return .done (.app f' x')
  | .lam n t b bi => do
    match ← instantiate1AndPostImpl t i val post, ← instantiate1AndPostImpl b (i+1) val post with
    | .yield t', .yield b'
    | .yield t', .done b'
    | .done t', .yield b' => post (.lam n t' b' bi)
    | .done t', .done b' => return .done (.lam n t' b' bi)
  | .forallE n t b bi => do
    match ← instantiate1AndPostImpl t i val post, ← instantiate1AndPostImpl b (i+1) val post with
    | .yield t', .yield b'
    | .yield t', .done b'
    | .done t', .yield b' => post (.forallE n t' b' bi)
    | .done t', .done b' => return .done (.forallE n t' b' bi)
  | .letE n t v b _ => do
    let t' ← instantiate1AndPostImpl t i val post
    match ← instantiate1AndPostImpl v i val post, ← instantiate1AndPostImpl b (i+1) val post with
    | .yield v', .yield b'
    | .yield v', .done b'
    | .done v', .yield b' => post (.letE n t'.val v' b' false)
    | .done v', .done b' => return .done (.letE n t'.val v' b' false)
  | .mdata _ e => instantiate1AndPostImpl e i val post
  | .proj n i e => do
    match ← instantiate1AndPostImpl e i val post with
    | .yield e' => post (.proj n i e')
    | .done e' => return .done (.proj n i e')
  | .mvar _ => do instantiate1AndPostImpl (← instantiateMVars e) i val post
  | e => return .done e


/-- Replaces free variable `fvar` with `val`. After replacement `post` is called
successively on the expressions with replaced fvar as long as it keeps returning
`ReplacePost.yield`

Example use: replace `x` with `(a,b,c)` in `fun y => x.1 + x.2.1 + y` and use
`post` to reduce projections resulting in `fun y => a + b + y`

-/
def replaceFVarAndPost (e : Expr) (fvar : FVarId) (val : Expr) (post : Expr → MetaM ReplacePost)
  : MetaM Expr := do pure (← replaceFVarAndPostImpl e fvar val post).val


/-- Instantiates the 0-th loose bound variable with `val`. After replacement `post` is called
successively on the expressions with replaced fvar as long as it keeps returning
`ReplacePost.yield`

Example use: replace `#0` with `(a,b,c)` in `fun y => #0.1 + #0.2.1 + y` and use
`post` to reduce projections resulting in `fun y => a + b + y`

Unlike `replaceFVarAndPost` this function can call `post e'` with `e'` containing
loose bounda variables
-/
def instantiate1AndPost (e : Expr) (val : Expr) (post : Expr → MetaM ReplacePost)
  : MetaM Expr := do pure (← instantiate1AndPostImpl e 0 val post).val



/--
Replaces all subexpresions in `e` that satisfy `f` with a free variables.

This function replaces only subexpressions that have no bound variables. -/
def replaceWithFVarsNoBVars (e : Expr) (f : Expr → MetaM Bool)
    (k : Array Expr  → Array Expr → Expr → MetaM α) : MetaM α := do

  let (e', vars) ←
    StateT.run (m:=MetaM) (σ := Array (FVarId×Expr)) (s:=#[]) do
      e.replaceM (fun e' => do
        if e'.hasLooseBVars then return .noMatch
        if ¬(← f e') then return .noMatch

        let fvarId ← mkFreshFVarId
        let fvar := Expr.fvar fvarId
        modify (fun vars => vars.push (fvarId, e'))
        return .yield fvar)

  let mut lctx ← getLCtx
  for (fvarId,val) in vars do
    lctx := (lctx.mkLocalDecl fvarId `x (← inferType val))

  withLCtx lctx (← getLocalInstances) do
    let vars := vars.map (fun (fvarId, val) => (Expr.fvar fvarId, val))
    let (fvars,vals) := vars.unzip
    k fvars vals e'
