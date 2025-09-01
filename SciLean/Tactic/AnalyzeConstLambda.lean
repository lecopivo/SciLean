import SciLean.Lean.Array
import SciLean.Lean.Expr
import SciLean.Lean.Meta.Basic

import SciLean.Data.ArraySet

open Lean Meta

namespace SciLean

structure ConstLambdaData where
  constName : Name
  mainArgs : Array Name
  unusedArgs : Array Name
  trailingArgs : Array Name
  mainIds : ArraySet Nat
  trailingIds : ArraySet Nat
  declSuffix : String

/-- Analyze function appearing in fprop rules or on lhs of ftrans rules  -/
def analyzeConstLambda (e : Expr) : MetaM ConstLambdaData := do
  let e ← zetaReduce e
  lambdaTelescope e fun xs b => do

    let constName ←
      match b.getAppFn' with
      | .const name _ => pure name
      | _ => throwError "{← ppExpr b.getAppFn'} is expected to be a constant"

    let args := b.getAppArgs
    let argNames ← getConstArgNames constName true

    -- check we have enough arguments
    if args.size < argNames.size then
      throwError "expression {← ppExpr b} is not fully applied, missing arguments {argNames[args.size:]}"
    if args.size > argNames.size then
      throwError "expression {← ppExpr b} is overly applied, surplus arguments {args[argNames.size:]}"

    if xs.size = 0 then
      return {
        constName := constName
        mainArgs := #[]
        unusedArgs := argNames
        trailingArgs := #[]
        mainIds := #[].toArraySet
        trailingIds := #[].toArraySet
        declSuffix := "arg"
      }

    let x := xs[0]!
    let xId := x.fvarId!
    let ys := xs[1:].toArray

    let mut main : Array Name := #[]
    let mut unused : Array Name := #[]
    let mut trailing : Array Name := #[]
    let mut mainIds : Array Nat := #[]
    let mut trailingIds : Array Nat := #[]

    for arg in args, i in [0:args.size] do
      let ys' := ys.filter (fun y => arg.containsFVar y.fvarId!)
      if ys'.size > 0 then
        if arg != ys'[0]! then
          throwError "invalid argument {← ppExpr arg}, trailing arguments {← ys.mapM ppExpr} can appear only as they are"
        trailing := trailing.push argNames[i]!
        trailingIds := trailingIds.push i
      else if arg.containsFVar xId then
        main := main.push argNames[i]!
        mainIds := mainIds.push i
      else
        unused := unused.push argNames[i]!

    let mut declSuffix := "arg"
    if main.size ≠ 0 then
      declSuffix := declSuffix ++ "_" ++ main.joinl (fun n => toString n) (·++·)
    if trailing.size ≠ 0 then
      declSuffix := declSuffix ++ "_" ++ trailing.joinl (fun n => toString n) (·++·)

    return {
      constName := constName
      mainArgs := main
      unusedArgs := unused
      trailingArgs := trailing
      mainIds := mainIds.toArraySet
      trailingIds := trailingIds.toArraySet
      declSuffix := declSuffix
    }
