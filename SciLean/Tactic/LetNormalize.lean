import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Conv.Basic

import SciLean.Lean.Meta.Basic
import SciLean.Lean.Expr

namespace SciLean.Meta

open Lean Meta Elab Tactic Conv

structure NormalizeLetConfig where
  removeTrivialLet := true
  splitStructureConstuctors := true
  reduceProjections := true

-- let x := 
--   let y := yValue
--   yBody
-- xBody

partial def normalizeLet (e : Expr) (config : NormalizeLetConfig := {}) : MetaM Expr := 
  match e.consumeMData with
  | .letE xName xType xValue xBody xNonDep => do
    match (← normalizeLet xValue config).consumeMData with
    | .letE yName yType yValue yBody yNonDep => 
      -- dbg_trace s!"{← ppExpr e}"
      -- dbg_trace s!"y := {← ppExpr yValue} : {← ppExpr yType} | x := {← ppExpr (yBody.instantiate1 yValue)}"
      -- dbg_trace "\n"
      withLetDecl yName yType yValue fun y => 
      withLetDecl xName xType (yBody.instantiate1 y) fun x => do
        mkLambdaFVars #[y,x] (xBody.instantiate1 x) >>= normalizeLet (config:=config)
    | xValue' => do

      if xValue.isFVar && config.removeTrivialLet then
        return ← normalizeLet (xBody.instantiate1 xValue) config

      -- deconstruct constructors into bunch of let bindings
      if let .some (ctor, args) := xValue.constructorApp? (← getEnv) then 
        if let .some info := getStructureInfo? (← getEnv) xType.getAppFn.constName! then
          let mut lctx ← getLCtx
          let insts ← getLocalInstances
          let mut fvars : Array Expr := #[]
          for i in [0:ctor.numFields] do
            let fvarId ← withLCtx lctx insts mkFreshFVarId
            let name := xName.appendAfter s!"_{info.fieldNames[i]!}"
            let val  := args[ctor.numFields + i]!
            let type ← inferType val
            lctx := lctx.mkLetDecl fvarId name type val (nonDep := false) default
            fvars := fvars.push (.fvar fvarId)

          let e' ← withLCtx lctx insts do
            let xValue' := mkAppN xValue.getAppFn (args[0:ctor.numFields].toArray.append fvars)
            mkLambdaFVars fvars (xBody.instantiate1 xValue')

          return (← normalizeLet e' config)

      -- in all other cases normalized the body
      let xBody' ← withLocalDecl xName default xType fun x =>
        normalizeLet (xBody.instantiate1 x) config >>= fun e => pure $ e.replaceFVar x (.bvar 0)
      pure $ .letE xName xType xValue' xBody' xNonDep

  | .app f x => do
    match (← normalizeLet f) with
    | .letE yName yType yValue yBody yNonDep => 
      normalizeLet (.letE yName yType yValue (.app yBody x) yNonDep) config
    | f' => 
      match (← normalizeLet x) with
      | .letE yName yType yValue yBody yNonDep => 
        normalizeLet (.letE yName yType yValue (.app f' yBody) yNonDep) config
      | x' => do
        if let .some e' ← reduceProjFn?' (f'.app x') then
          pure e'
        else
          pure (f'.app x')
  | e => pure e


open Lean Meta Qq in
#eval show MetaM Unit from do

  let e := q(
    let x3 :=
      let x2 := 
        let x1 := 10
        x1 + 5
      x2
    let h1 := 
      let h2 := 2
      h2 + 1
    let y5 := 
      let y1 := 4
      let y2 := 5
      (let y3 := 14; let f1 := fun x => let fy1 := 5; x + 100 + fy1; y1 + y3 + f1 h1) + (let y4 := 56; y2 + y4)
    let z3 :=
      (let z1 := 1; z1 + z1, let z2 := 2; z2 * z2)
    x3 + y5 + z3.1 + z3.2)

  IO.println s!"{← ppExpr e}\n"
  
  let e' ← normalizeLet e
  IO.println s!"{← ppExpr e'}\n"

  if ¬(← isDefEq e e') then
    throwError "!!!not defEq!!!"

  let e'' ← normalizeLet e'


syntax (name := let_flatten) " let_flatten " : conv 

@[tactic let_flatten] 
def convLetFlatten : Tactic
| `(conv| let_flatten) => do  
  (← getMainGoal).withContext do
    let lhs ← getLhs
    let lhs' ← flattenLet 100 lhs
    
    changeLhs lhs'
| _ => Lean.Elab.throwUnsupportedSyntax
