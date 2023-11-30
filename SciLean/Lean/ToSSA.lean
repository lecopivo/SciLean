import Lean
import Qq

open Lean Meta

namespace Lean.Expr

/-- Turns expression `e` into single-static-assigment w.r.t. to free variables `fvars` and all bound variables

Returns expression, newly introduced let bindings and local context where these bindings live

--TODO: add option to do common subexpression elimination i.e. check if let binding with particular value already exists
-/
partial def toSSA.impl (e : Expr) (fvars : Array Expr) : MetaM (Expr × Array Expr × LocalContext) := do
  match e with
  | .app .. => do
    let fn := e.getAppFn
    let args := e.getAppArgs
    let infos := (← getFunInfoNArgs fn args.size).paramInfo
    goApp fn args infos fvars 0 #[]
  | .lam n t b bi => 
    withLocalDecl n bi t fun x => do
      let b := b.instantiate1 x
      let lctx ← getLCtx
      let (b', lets, lctx') ← impl b (fvars.push x)
      withLCtx lctx' (← getLocalInstances) do
        return (← mkLambdaFVars (#[x]++lets) b', #[], lctx)
  | .letE n t v b _ => do
    let (v', lets, lctx') ← impl v fvars
    withLCtx lctx' (← getLocalInstances) do
      withLetDecl n t v' fun x => do
        let b := b.instantiate1 x
        let (b', lets', lctx'') ← impl b (fvars ++ lets.push x)
        withLCtx lctx'' (← getLocalInstances) do
          return (b', lets.push x ++ lets', ← getLCtx)
  | .mdata _ e => impl e fvars
  | _ => return (e,#[],←getLCtx)
where
  goApp (fn : Expr) (args : Array Expr) (infos : Array ParamInfo) (fvars : Array Expr) (i : Nat) (lets : Array Expr)  : MetaM (Expr × Array Expr × LocalContext) := do
      if h : i < args.size then do

        if h' : i < infos.size then
          let info := infos[i]!
          if info.isImplicit || info.isInstImplicit then
            return ← goApp fn args infos fvars (i+1) lets

        let arg := args[i]
        let (arg', lets', lctx') ← toSSA.impl arg fvars 
        withLCtx lctx' (← getLocalInstances) do
          if arg'.consumeMData.isApp then
            withLetDecl Name.anonymous (← inferType arg') arg' fun argVar => do
              goApp fn (args.set ⟨i,h⟩ argVar) infos (fvars.push argVar) (i+1) (lets ++ lets'.push argVar)
          else
            goApp fn (args.set ⟨i,h⟩ arg') infos fvars (i+1) (lets++lets')
      else
        return (mkAppN fn args, lets, ← getLCtx)

/-- Converts an expression to single static assigment form w.r.t. bound variables and free variables `fvars`

Examples:
- `x*x + x ==> let a := x*x; a + x`
- `fun y => x*y + x*x ==> fun y => let a := x*y; let a_1 := x*x; a + a_1`
-/
def toSSA (e : Expr) (fvars : Array Expr) : MetaM Expr := do
  let (e',lets,lctx) ← toSSA.impl e fvars
  withLCtx lctx (← getLocalInstances) do
    let e'' ← mkLambdaFVars lets e'
    if ¬(← isDefEq e e'') then
      throwError "ssa form is not defEq to the original!"
    return e''


-- open Qq Elab Term
-- #eval show TermElabM Unit from do 

--   withLocalDeclDQ `x q(Nat) fun x => do

--     let e := q( fun y => $x*y + $x*$x)

--     let e' ← toSSA e #[x]
--     IO.println (← ppExpr e)
--     IO.println ""
--     IO.println (← ppExpr e')
--     IO.println ""


--   withLocalDeclDQ `x q(Nat) fun x => do

--     let e := q( fun y : Nat => (($x*$x*y + $x^2) + $x*y + $x, fun z : Nat => z*y*$x + $x))

--     let e' ← toSSA e #[x]
--     IO.println (← ppExpr e)
--     IO.println ""
--     IO.println (← ppExpr e')


--   withLocalDeclDQ `x q(Nat) fun x => do
--   withLocalDeclDQ `f q(Nat→Nat) fun f => do

--     let e := q(fun y : Nat => ($f y, fun dy => (($f $x) * $f y * $f dy)))

--     let e' ← toSSA e #[x]
--     IO.println (← ppExpr e)
--     IO.println ""
--     IO.println (← ppExpr e')
