import Lean
import Mathlib.Lean.Meta.RefinedDiscrTree


import SciLean.Tactic.GTrans.Decl
import SciLean.Lean.Meta.Basic

open Lean Meta
open Mathlib.Meta.FunProp

namespace SciLean.Tactic.GTrans


/-- Generalized transformation theorem -/
structure GTransTheorem where
  /-- Name of generalized transformation -/
  gtransName : Name
  /-- Name of lambda theorem -/
  thmName : Name
  /-- discrimination tree keys used to index this theorem -/
  keys        : List RefinedDiscrTree.Key
  /-- priority -/
  priority    : Nat  := eval_prio default
  deriving Inhabited, BEq


/-- Entry for the `GTransTheorems` extension. -/
structure GTransEntry where
  thm : GTransTheorem
  keysWithLazy : List (RefinedDiscrTree.Key × RefinedDiscrTree.LazyEntry)
  deriving Inhabited



/-- Get proof of a theorem. -/
def GTransTheorem.getProof (thm : GTransTheorem) : MetaM Expr := do
  mkConstWithFreshMVarLevels thm.thmName


open Mathlib.Meta.FunProp in
/-- Storage for registered generalized-transformation theorems. -/
structure GTransTheorems where
  /-- Discrimination tree indexed by generalized-transformation theorem keys. -/
  theorems     : RefinedDiscrTree GTransTheorem := {}
  deriving Inhabited

/-- Extension type storing generalized-transformation theorem entries. -/
abbrev GTransTheoremsExt := SimpleScopedEnvExtension GTransEntry GTransTheorems


open Mathlib.Meta.FunProp in
/-- Register generalized-transformation theorems in the scoped extension. -/
initialize gtransTheoremsExt : GTransTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name     := by exact decl_name%
    initial  := {}
    addEntry := fun d e =>
      let thm := e.thm
      {d with theorems := e.keysWithLazy.foldl (fun thms (key, lazy) =>
        RefinedDiscrTree.insert thms key (lazy, thm)) d.theorems}
  }



def getTheoremFromConst (declName : Name) (prio : Nat := eval_prio default) : MetaM GTransTheorem := do
  let info ← getConstInfo declName

  let (_,_,b) ← forallMetaTelescope info.type

  Meta.letTelescope b fun _ b => do

  let .some gtransDecl ← isGTrans? b
    | throwError s!"not generalized transformation {← ppExpr b} \n \n {← ppExpr (← whnfR b)}"


  -- replace output arguments with meta variables, we do not want to index them!
  let mut (fn,args) := b.withApp (fun fn args => (fn,args))
  for i in gtransDecl.outputArgs do
    let X ← inferType args[i]!
    args := args.set! i (← mkFreshExprMVar X)

  let b := fn.beta args
  let keysWithLazy ← RefinedDiscrTree.initializeLazyEntryWithEta b
  let keys := keysWithLazy.map (·.1)

  let thm : GTransTheorem := {
    gtransName := gtransDecl.gtransName
    thmName := declName
    keys    := keys
    priority  := prio
  }
  return thm


def getEntryFromConst (declName : Name) (prio : Nat := eval_prio default) : MetaM GTransEntry := do
  let thm ← getTheoremFromConst declName prio

  let info ← getConstInfo declName
  let (_,_,b) ← forallMetaTelescope info.type
  Meta.letTelescope b fun _ b => do
  let .some gtransDecl ← isGTrans? b | unreachable!
  let (fn,args) := b.withApp (fun fn args => (fn,args))
  let mut args := args
  for i in gtransDecl.outputArgs do
    let X ← inferType args[i]!
    args := args.set! i (← mkFreshExprMVar X)
  let b := fn.beta args
  let keysWithLazy ← RefinedDiscrTree.initializeLazyEntryWithEta b
  return { thm := thm, keysWithLazy := keysWithLazy }




def addTheorem (declName : Name) (kind : AttributeKind := .global) (prio : Nat := eval_prio default) : MetaM Unit := do

  let entry ← getEntryFromConst declName prio

  gtransTheoremsExt.add entry kind
