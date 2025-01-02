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
  keys        : List RefinedDiscrTree.DTExpr
  /-- priority -/
  priority    : Nat  := eval_prio default
  deriving Inhabited, BEq



/-- Get proof of a theorem. -/
def GTransTheorem.getProof (thm : GTransTheorem) : MetaM Expr := do
  mkConstWithFreshMVarLevels thm.thmName


open Mathlib.Meta.FunProp in
/-- -/
structure GTransTheorems where
  /-- -/
  theorems     : RefinedDiscrTree GTransTheorem := {}
  deriving Inhabited

/-- -/
abbrev GTransTheoremsExt := SimpleScopedEnvExtension GTransTheorem GTransTheorems


open Mathlib.Meta.FunProp in
/-- -/
initialize gtransTheoremsExt : GTransTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name     := by exact decl_name%
    initial  := {}
    addEntry := fun d e =>
      {d with theorems := e.keys.foldl (RefinedDiscrTree.insertDTExpr · · e) d.theorems}
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

  let thm : GTransTheorem := {
    gtransName := gtransDecl.gtransName
    thmName := declName
    keys    := ← RefinedDiscrTree.mkDTExprs b false
    priority  := prio
  }
  return thm




def addTheorem (declName : Name) (kind : AttributeKind := .global) (prio : Nat := eval_prio default) : MetaM Unit := do

  let thm ← getTheoremFromConst declName prio

  gtransTheoremsExt.add thm kind
