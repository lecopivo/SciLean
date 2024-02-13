import Lean
import SciLean.Lean.Meta.Basic
import SciLean.Lean.Meta.Structure

namespace SciLean.Tactic

open Lean Meta Simp

initialize registerTraceClass `Meta.Tactic.let_normalize

#check Simp.Step

theorem let_congr_eq {α : Sort u} {β : Sort v} {a a' : α} {b b' : α → β}
    (h₁ : a = a') (h₂ : ∀ x, x = a' → b x = b' x) : (let x := a; b x) = (let x := a'; b' x) :=
by
  rw[h₁]; rw[h₂ a' rfl]

private def mkLetCongrEq (h₁ h₂ : Expr) : MetaM Expr :=
  mkAppM ``let_congr_eq #[h₁, h₂]


def letFinalize (n : Name) (t x : Expr) (rv rbx : Result) : MetaM Result := do

  let e' := mkLet n t rv.expr (← rbx.expr.abstractM #[x])
  let hb? ← match rbx.proof? with
    | none => pure none
    | some h => pure (some (← mkLambdaFVars #[x] h))

  match rv.proof?, hb? with
  | none,    none    => return { expr := e' }
  | some h,  none    => return { expr := e', proof? := some (← mkLetValCongr (← mkLambdaFVars #[x] rbx.expr) h) }
  | none,    some h  => return { expr := e', proof? := some (← mkLetBodyCongr rv.expr h) }
  | some hv, some hb => return { expr := e', proof? := some (← mkLetCongr hv hb) }



/-- Merge two sets of free variables where `fvars2` can depend on `fvars1`.
It tries to push free variables in `fvars2` to the front as much as possible.

The main application is to move let bindings out of lambdas, consider expression:
```
  fun x y =>
    let a := x
    let b := a + y
    let c := 42
    ..
```
calling `mergeFVars #[x,y] #[a,b,c]` will return `#[c,x,a,y,b] thus we can rewrite
above functions as
```
  let c := 42
  fun x =>
    let a := x
    fun y =>
      let b := a + y
      ..
```
 -/
private def mergeFVars (fvars1 fvars2 : Array Expr) : MetaM (Array Expr) := do
  let (a,b) ← fvars1.foldrM (init := (fvars2, (#[] : Array Expr)))
    fun fvar (fvars, r) => do
      let deps ← collectForwardDeps #[fvar] false
      let (fvarsDep, fvarsNoDep) := fvars.partition deps.contains
      pure (fvarsNoDep, #[fvar]++fvarsDep++r)
  let r := a ++ b
  return r


/-- Is `e` in the form `p₁ (...(pₙ x))` where `pᵢ` are projections and `x` free variable?
-/
def isProjectionOfFVar (e : Expr) : MetaM Bool := do
  match e with
  | .mdata _ e => isProjectionOfFVar e
  | .fvar _ => return true
  | .proj _ _ x => isProjectionOfFVar x
  | .app f x =>
    let some projName := f.getAppFn'.constName? | return false
    let some info ← getProjectionFnInfo? projName | return false
    if info.numParams = f.getAppNumArgs then
      isProjectionOfFVar x
    else
      return false
  | _ => return false


def doRemoveLet (v : Expr) : MetaM Bool := do
  if v.isFVar then
    return true
  else if ← isProjectionOfFVar v then
    return true
  else if
    (v.isAppOfArity ``OfNat.ofNat 3 ||
     v.isAppOfArity ``OfScientific.ofScientific 5) then
    return true
  -- else if v.isLambda then
  --   return true
  else
    return false


def removeLet? (rv : Result) (n : Name) (t b : Expr) : SimpM (Option Result) := do

  unless ← doRemoveLet rv.expr do return none

  let rbx ←
    withTraceNode `Meta.Tactic.let_normalize
      (fun _ => return s!"body - remove") do
    simp (b.instantiate1 rv.expr)

  let f := Expr.lam n t b default
  let proof? ← do
    match rv.proof? with
    | none => pure none
    | some h => pure <| .some (← mkLetValCongr f h)

  let r : Result := { expr := f.app rv.expr, proof? := proof? }
  return .some (← r.mkEqTrans rbx)


/--
  If `rv.expr` is a application of structure constructor then it is deconstructed into multiple
  let bindings and passed on to `b`

Example:
```
let n := (a,b,c)
b
```
gets turned into
```
let n1 := a
let n2 := b
let n3 := c
b'
```
where `b'` is simplified `b[v := (v1,v2,v3)]`
-/
def letSplit? (rv : Result) (n : Name) (t b : Expr) : SimpM (Option Result) := do
  let .some (vs, projs, mk) ← splitByCtors? rv.expr | return none

  let names := (Array.range vs.size).map fun i => n.appendAfter (toString i)
  let e' ←
    withLetDecls names vs fun fvars' =>
      mkLetFVars fvars' (b.instantiate1 (mk.beta fvars'))
  let r : Simp.Result ← do
    let b' ←
      withLocalDeclD n t fun x => do
        mkLambdaFVars #[x] (b.instantiate1 (mk.beta <| projs.map (fun proj => proj.beta #[x])))
    let proof ← mkLetValCongr b' (← rv.getProof)
    pure ({ expr := e', proof? := .some proof } : Result)

  let r' ←
    withTraceNode `Meta.Tactic.let_normalize
      (fun _ => return s!"body - split") do
      simp e'
  return .some (← r.mkEqTrans r')



def letFlatten? (rv : Result) (n : Name) (t b : Expr) : SimpM (Option Result) := do

  unless rv.expr.isLet do return none

  withLocalDeclD n t fun x => do

    let bx := b.instantiate1 x
    let rbx ←
      withTraceNode `Meta.Tactic.let_normalize
        (fun _ => return s!"body - flatten") do
        simp bx

    letTelescope rv.expr fun xs rvb => do
      withLetDecl n t rvb fun x' => do
      let r ← letFinalize n t x rv rbx
      let r := {r with expr := ← mkLambdaFVars (xs.push x') (rbx.expr.replaceFVar x x') }
      return some r


def letCase (e : Expr) : SimpM Step := do

  let Expr.letE n t v b _ := e | unreachable!

  withTraceNode `Meta.Tactic.let_normalize
    (fun _ => return s!"normalizing let {n} := {v.ctorName}, {b.ctorName}") do


  if (← Simp.getConfig).zeta then
    return .continue <| some { expr := b.instantiate1 v }
  else
    match (← getSimpLetCase n t b) with
    | SimpLetCase.dep => return .continue <| some { expr := (← dsimp e) }
    | SimpLetCase.nondep =>
      withTraceNode `Meta.Tactic.let_normalize
        (fun _ => return s!"hihi") do

      let rv ←
          withTraceNode `Meta.Tactic.let_normalize
            (fun _ => return s!"value") do
          simp v

      if let .some r ← removeLet? rv n t b then
        return .continue <| some r

      if let .some r ← letSplit? rv n t b then
        return .continue <| some r

      if let .some r ← letFlatten? rv n t b then
        return .done <|  r

      withLocalDeclD n t fun x => do
        let bx := b.instantiate1 x
        let rbx ←
          withTraceNode `Meta.Tactic.let_normalize
            (fun _ => return s!"body") do
            simp bx
        return .continue <| some (← letFinalize n t x rv rbx)
    | SimpLetCase.nondepDepVar =>
      let v' ← dsimp v
      withLocalDeclD n t fun x => do
        let bx := b.instantiate1 x
        let rbx ← simp bx
        return .continue <| some (← letFinalize n t x {expr:=v'} rbx)


def lambdaCase (e : Expr) : SimpM Step := do

  withTraceNode `Meta.Tactic.let_normalize (fun _ => return s!"normalizing lambda") do

    withParent e <| lambdaTelescopeDSimp e fun xs e => withNewLemmas xs do
      let r ←
        withTraceNode `Meta.Tactic.let_normalize
          (fun _ => return s!"lambda body") do
        simp e
      letTelescope r.expr fun ys b => do
        let xs' ← mergeFVars xs ys
        let eNew ← mkLambdaFVars xs' b
        match r.proof? with
        | none   => return .continue <| some { expr := eNew }
        | some h =>
          let p ← xs.foldrM (init := h) fun x h => do
            mkFunExt (← mkLambdaFVars #[x] h)
          return .continue <| some { expr := eNew, proof? := p }



simproc_decl let_normalize (_) := fun e => do

  match e with
  | .letE .. => return ← letCase e
  | .lam .. => return ← lambdaCase e
  | _ => return .continue
