import Lean
import Mathlib.Lean.Meta.RefinedDiscrTree


open Lean Meta
open Mathlib.Meta.FunProp

namespace SciLean.Tactic.DataSynth

structure DataSynthDecl where
  name : Name
  nargs : Nat
  outputArgs : Array Nat
  inputArg : Option Nat
  deriving Hashable, Inhabited, BEq

/-- Discrimination tree for function properties. -/
structure DataSynthDecls where
  /-- Discrimination tree for function properties. -/
  decls : NameMap DataSynthDecl := {}
  deriving Inhabited

/-- -/
abbrev DataSynthDeclsExt := SimpleScopedEnvExtension DataSynthDecl DataSynthDecls

initialize dataSynthDeclsExt : DataSynthDeclsExt ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun d e =>
      {d with decls := d.decls.insert e.name e}
  }


def getDataSynth (dataSynthName : Name) : MetaM DataSynthDecl := do
  return (dataSynthDeclsExt.getState (← getEnv)).decls.find! dataSynthName


def addDataSynthDecl (declName : Name) (outArgs : Array Name) (inArg? : Option Name) : MetaM Unit := do

  let info ← getConstInfo declName

  let (xs,_,_) ← forallMetaTelescope info.type

  let argNames ←
    forallTelescope info.type fun xs _ =>
      xs.mapM (fun x => x.fvarId!.getUserName)

  -- if ¬b.isProp then
  --   throwError "invalid data synthesis declaration, has to be `Prop` valued function"

  -- convert names to indices
  let outputArgs : Array Nat ←
    outArgs.mapM (fun arg => do
      let some i := argNames.findIdx? (arg==·)
        | throwError "argument {arg} not found"
      pure i)

  let inArg? : Option Nat ←
    inArg?.mapM fun arg => do
      let some i := argNames.findIdx? (arg==·)
        | throwError "argument {arg} not fuound"
      unless (← inferType xs[i]!).isForall do
        throwError "input argument {arg} is expected to be function type"
      pure i

  if outputArgs.size = 0 then
    throwError "expected at least one output argument"

  let decl : DataSynthDecl := {
    name := declName
    nargs := xs.size
    outputArgs := outputArgs
    inputArg := inArg?
  }

  modifyEnv (dataSynthDeclsExt.addEntry · decl)


def isDataSynth? (e : Expr) : MetaM (Option DataSynthDecl) := do

  let e ← whnfR e

  let ext := dataSynthDeclsExt.getState (← getEnv)

  let .some (fnName,_) := e.getAppFn'.const?
    | return none

  let .some DataSynthDecl := ext.decls.find? fnName
    | return none

  if e.getAppNumArgs' = DataSynthDecl.nargs then
    return DataSynthDecl
  else
    return none
