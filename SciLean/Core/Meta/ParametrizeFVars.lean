import Lean
import Qq

import Std.Tactic.GuardMsgs
import SciLean.Lean.Meta.Basic

open Lean Meta Qq

namespace SciLean

variable {α : Type _} 
variable [MonadControlT MetaM n] [Monad n]


private def withParametrizedFVarsImpl (w : Expr) (vars vals : Array Expr) 
  (k : Array Expr → Array Expr → MetaM α) : MetaM α := do
  let mut vals := vals
  let mut lctx ← getLCtx
  
  let wId := w.fvarId!
  let wName ← wId.getUserName
  let W ← inferType w

  let mut fvarSet : FVarIdSet := .fromArray (vars.map (fun var => var.fvarId!)) _
  let mut replaceFVars : Array Expr := vars
  let mut replaceVals  : Array Expr := vars.map (fun var => var.app w)

  let mut vars' : Array Expr := #[]

  for id in lctx.getFVarIds do
    let decl := lctx.get! id
    if decl.isLet then
      throwError "variable parametrization can't handle let bindings right now"
    let type := decl.type.replaceFVars replaceFVars replaceVals
    if type.containsFVar wId then
      lctx := lctx.modifyLocalDecl id (fun d => d.setType type)
      vars' := vars'.push (.fvar id)
      if ¬(fvarSet.contains id) then
        fvarSet := fvarSet.insert id
        replaceFVars := replaceFVars.push (.fvar id)
        replaceVals := replaceVals.push ((Expr.fvar id).app w)
    else if fvarSet.contains id then
      vars' := vars'.push (.fvar id)

  for var in vars do
    let id := var.fvarId!
    let decl := lctx.get! id
    let type := Expr.forallE wName W (decl.type.abstract #[w]) .default
    lctx := lctx.modifyLocalDecl id (fun d => d.setType type)


  for id in lctx.getFVarIds do
    let decl := lctx.get! id
    if decl.type.containsFVar wId then
      let type := Expr.forallE wName W (decl.type.abstract #[w]) .default
      lctx := lctx.modifyLocalDecl id (fun d => d.setType type)

  let vals' := vals.map (fun val => val.replaceFVars replaceFVars replaceVals)

  withLCtx lctx (← getLocalInstances) (k vars' vals')


/-- 
Modifies the local context such that all free variables `vars` are turned from 
`x : X` into `x : W → X` and replaces all occurances of `x` with `x w` in `vals`.

The callback `k` is called as `k vars' vals'` where:
- `vars'` is an array containing all fvars that have been parametrized
  parametrizing fvars can cause other fvars to be parametrized too thus `vars'`
  can differ from `vars`
- `vals'` are values with original vars `x` replaced with `x w`

Example of parametrizing local context:
```
α : Sort u
c : Prop
h : Decidable c
t : α
e : α
```
with `vars := #[c,t]` and `vals := #[Decidable.casesOn h (fun x => e) fun x => t]`
produces local context
```
α : Sort u
c : W → Prop
h : (w : W) → Decidable (c w)
t : W → α
e : α
```
and calls `k #[c,h,t] #[Decidable.casesOn (h w) (fun x => e) fun x => t w]`
-/
def withParametrizedFVars (w : Expr) (vars vals : Array Expr) 
  (k : Array Expr → Array Expr → n α) : n α := do
  map2MetaM (fun k => withParametrizedFVarsImpl w vars vals k) k


/--
info: Decidable.casesOn h (fun x => e) fun x => t
α : Sort u
c : W → Prop
h : (w : W) → Decidable (c w)
t : W → α
e : α
W : Type
w : W
#[c, h, t]
#[Decidable.casesOn (h w) (fun x => e) fun x => t w]
-/
#guard_msgs in
#eval show MetaM Unit from do

  let info ← getConstInfoDefn ``ite

  lambdaTelescope info.value fun xs b => do

    IO.println (← ppExpr b)


    withLocalDecl `W .default q(Type) fun W => 
    withLocalDecl `w .default W fun w => do

      let vars := #[xs[1]!, xs[3]!]
      withParametrizedFVars w vars #[b] fun vars' vals' => do

        IO.println (← (← getLCtx).toString)
        IO.println (← vars'.mapM ppExpr)
        IO.println (← vals'.mapM ppExpr)

