import Lean
import Qq
import SciLean.Tactic.GTrans.MetaLCtxM

open Lean Meta

namespace Lean.Expr

/-- Turns expression `e` into single-static-assigment w.r.t. to free variables `fvars` and all bound variables

Returns expression, newly introduced let bindings
-/
partial def toSSACore (e : Expr) (fvars : Array Expr) : MetaLCtxM (Expr × Array Expr) := do
  -- todo: use some fast data structure for this look up
  if let .some e' ← fvars.findM? (fun v => isDefEq e v) then
    return (e',#[])
  else
  match e with
  | .app .. => do
    let fn := e.getAppFn
    let args := e.getAppArgs
    let infos := (← getFunInfoNArgs fn args.size).paramInfo
    goApp fn args infos fvars 0 #[]

  | .lam n t b bi =>
    let x ← introLocalDecl n bi t
    let b := b.instantiate1 x
    let (b', lets) ← toSSACore b (fvars.push x)
    return (← mkLambdaFVars (#[x]++lets) b', #[])

  | .letE n t v b _ => do
    let (v', lets) ← toSSACore v fvars
    -- introduce new let binding if `v'` is not a free variables
    let (v'',lets) ← if v'.isFVar then  pure (v',lets) else
      let v'' ← introLetDecl n t v'
      pure (v'', lets.push v'')
    let (b', lets') ← toSSACore (b.instantiate1 v'') (fvars++lets)
    return (b',lets++lets')

  | .mdata _ e => toSSACore e fvars
  | _ => return (e,#[])
where
  goApp (fn : Expr) (args : Array Expr) (infos : Array ParamInfo) (fvars : Array Expr) (i : Nat) (lets : Array Expr) : MetaLCtxM (Expr × Array Expr) := do
      if h : i < args.size then do
        if h' : i < infos.size then
          let info := infos[i]!
          if info.isImplicit || info.isInstImplicit then
            return ← goApp fn args infos fvars (i+1) lets

        let arg := args[i]
        let (arg', lets') ← toSSACore arg fvars
          if arg'.consumeMData.isApp then
            let arg'' ← introLetDecl Name.anonymous (← inferType arg') arg'
            goApp fn (args.set i arg'' h) infos (fvars.push arg'') (i+1) (lets ++ lets'.push arg'')
          else
            goApp fn (args.set i arg' h) infos fvars (i+1) (lets++lets')
      else
        return (mkAppN fn args, lets)


/-- Converts an expression to single static assigment form w.r.t. bound variables and free variables `fvars`

Examples:
- `x*x + x ==> let a := x*x; a + x`
- `fun y => x*y + x*x ==> fun y => let a := x*y; let a_1 := x*x; a + a_1`
-/
def toSSA (e : Expr) (fvars : Array Expr) : MetaM Expr := do
  (toSSACore e fvars).runInMeta fun (e',lets) => do
    let e' ← mkLambdaFVars lets e'
    if ¬(← isDefEq e e') then
      throwError "ssa form is not defEq to the original!"
    return e'


open Parser.Tactic in
-- todo: add option that ssa form should be done w.r.t. to particular variables
/-- `to_ssa` converts expression to single static assigment form -/
syntax (name:=to_ssa_conv) "to_ssa" : conv

open Lean Meta Elab Tactic
@[tactic to_ssa_conv] unsafe def toSSAConv : Tactic
| `(conv| to_ssa) => do
  let e ← Conv.getLhs
  -- for some reason we often need to call `to_ssa` twice so let's call it twice right away
  Conv.changeLhs (← toSSA (← toSSA e #[]) #[])
| _ => throwUnsupportedSyntax
