import Lean
import Qq

open Lean Meta

namespace Lean.Expr

/-- Turns expression `e` into single-static-assigment w.r.t. to free variables `fvars` and all bound variables

Returns expression, newly introduced let bindings and local context where these bindings live
-/
partial def toSSA.impl (e : Expr) (fvars : Array Expr) : MetaM (Expr × Array Expr × LocalContext) := 
  if ¬(e.hasAnyFVar (fun id => fvars.contains (.fvar id))) then
    return (e,#[],←getLCtx)
  else
    match e with
    | .app .. => do
      let fn := e.getAppFn
      let args := e.getAppArgs
      goApp fn args fvars 0 #[]
    | .lam n t b bi => 
      withLocalDecl n bi t fun x => do
        let b := b.instantiate1 x
        let lctx ← getLCtx
        let (b', lets, lctx') ← impl b (fvars.push x)
        withLCtx lctx' (← getLocalInstances) do
          return (← mkLambdaFVars (#[x]++lets) b', #[], lctx)
    | .mdata _ e => impl e fvars
    | _ => return (e,#[],←getLCtx)
where
  goApp (fn : Expr) (args : Array Expr) (fvars : Array Expr) (i : Nat) (lets : Array Expr)  : MetaM (Expr × Array Expr × LocalContext) := do
      if h : i < args.size then
        let arg := args[i]
        let (arg', lets', lctx') ← toSSA.impl arg fvars 
        withLCtx lctx' (← getLocalInstances) do
          if ¬(arg'.hasAnyFVar (fun id => fvars.contains (.fvar id))) && lets'.size = 0 then
            goApp fn args fvars (i+1) lets
          else
            if arg'.isApp then
              withLetDecl Name.anonymous (← inferType arg') arg' fun argVar => do
                goApp fn (args.set ⟨i,h⟩ argVar) (fvars.push argVar) (i+1) (lets ++ lets'.push argVar)
            else
              goApp fn (args.set ⟨i,h⟩ arg') fvars (i+i) (lets++lets')
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


open Qq
#eval show MetaM Unit from do 

  withLocalDeclDQ `x q(Nat) fun x => do

    let e := q( fun y => $x*y + $x*$x)

    let e' ← toSSA e #[x]
    IO.println (← ppExpr e)
    IO.println ""
    IO.println (← ppExpr e')
    IO.println ""


  withLocalDeclDQ `x q(Nat) fun x => do

    let e := q( fun y : Nat => (($x*$x*y + $x^2) + $x*y + $x, fun z : Nat => z*y*$x + $x))

    let e' ← toSSA e #[x]
    IO.println (← ppExpr e)
    IO.println ""
    IO.println (← ppExpr e')
