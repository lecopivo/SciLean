import Lean
import Mathlib.Tactic.FunProp.RefinedDiscrTree

import SciLean.Tactic.DataSynth.Decl
import SciLean.Lean.Meta.Basic

open Lean Meta
open Mathlib.Meta.FunProp

namespace SciLean.Tactic.DataSynth


/-- Generalized transformation theorem -/
structure DataSynthTheorem where
  /-- Name of generalized transformation -/
  name : Name
  /-- Name of lambda theorem -/
  thmName : Name
  /-- discrimination tree keys used to index this theorem -/
  keys        : List RefinedDiscrTree.DTExpr
  /-- priority -/
  priority    : Nat  := eval_prio default
  deriving Inhabited, BEq



/-- Get proof of a theorem. -/
def DataSynthTheorem.getProof (thm : DataSynthTheorem) : MetaM Expr := do
  mkConstWithFreshMVarLevels thm.thmName


open Mathlib.Meta.FunProp in
/-- -/
structure DataSynthTheorems where
  /-- -/
  theorems     : RefinedDiscrTree DataSynthTheorem := {}
  deriving Inhabited

/-- -/
abbrev DataSynthTheoremsExt := SimpleScopedEnvExtension DataSynthTheorem DataSynthTheorems


open Mathlib.Meta.FunProp in
/-- -/
initialize dataSynthTheoremsExt : DataSynthTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name     := by exact decl_name%
    initial  := {}
    addEntry := fun d e =>
      {d with theorems := e.keys.foldl (RefinedDiscrTree.insertDTExpr · · e) d.theorems}
  }



def getTheoremFromConst (declName : Name) (prio : Nat := eval_prio default) : MetaM DataSynthTheorem := do
  let info ← getConstInfo declName

  let (_,_,b) ← forallMetaTelescope info.type

  Meta.letTelescope b fun _ b => do

  let .some dataSynthDecl ← isDataSynth? b
    | throwError s!"not generalized transformation {← ppExpr b} \n \n {← ppExpr (← whnfR b)}"


  -- replace output arguments with meta variables, we do not want to index them!
  let mut (fn,args) := b.withApp (fun fn args => (fn,args))
  for i in dataSynthDecl.outputArgs do
    let X ← inferType args[i]!
    args := args.set! i (← mkFreshExprMVar X)

  let b := fn.beta args

  let thm : DataSynthTheorem := {
    name := dataSynthDecl.name
    thmName := declName
    keys    := ← RefinedDiscrTree.mkDTExprs b {} false
    priority  := prio
  }
  return thm


def addTheorem (declName : Name) (kind : AttributeKind := .global) (prio : Nat := eval_prio default) : MetaM Unit := do


  let thm ← getTheoremFromConst declName prio

  dataSynthTheoremsExt.add thm kind
