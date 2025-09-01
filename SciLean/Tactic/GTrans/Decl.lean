import Lean
import Mathlib.Lean.Meta.RefinedDiscrTree


open Lean Meta
open Mathlib.Meta.FunProp

namespace SciLean.Tactic.GTrans


structure GTransDecl where
  gtransName : Name
  nargs : Nat
  outputArgs : Array Nat
  deriving Inhabited, BEq

/-- Discrimination tree for function properties. -/
structure GTransDecls where
  /-- Discrimination tree for function properties. -/
  decls : NameMap GTransDecl := {}
  deriving Inhabited

/-- -/
abbrev GTransDeclsExt := SimpleScopedEnvExtension GTransDecl GTransDecls

initialize gtransDeclsExt : GTransDeclsExt ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun d e =>
      {d with decls := d.decls.insert e.gtransName e}
  }


def getGTrans (gtransName : Name) : MetaM GTransDecl := do
  return (gtransDeclsExt.getState (← getEnv)).decls.find! gtransName


def addGTransDecl (declName : Name) : MetaM Unit := do

  let info ← getConstInfo declName

  let (xs,_,b) ← forallMetaTelescope info.type

  if ¬b.isProp then
    throwError "invalid generalized transformation declaration, has to be `Prop` valued function"

  let mut outputArgs : Array Nat := #[]
  for x in xs, i in [0:xs.size] do

    if (← inferType x).isAppOf ``outParam then
      outputArgs := outputArgs.push i

  if outputArgs.size = 0 then
    throwError "generalized transformation is expected to have at least one output argument"

  let decl : GTransDecl := {
    gtransName := declName
    nargs := xs.size
    outputArgs := outputArgs
  }

  modifyEnv (gtransDeclsExt.addEntry · decl)


def isGTrans? (e : Expr) : MetaM (Option GTransDecl) := do

  let e ← whnfR e

  let ext := gtransDeclsExt.getState (← getEnv)

  let .some (fnName,_) := e.getAppFn'.const?
    | return none

  let .some gtransDecl := ext.decls.find? fnName
    | return none

  if e.getAppNumArgs' = gtransDecl.nargs then
    return gtransDecl
  else
    return none
