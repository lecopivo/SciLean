import Lean
import Mathlib.Lean.Meta.RefinedDiscrTree

import SciLean.Tactic.DataSynth.Decl
import SciLean.Lean.Meta.Basic

open Lean Meta
open Mathlib.Meta.FunProp

namespace SciLean.Tactic.DataSynth


inductive LambdaTheorem where
  /-- Composition theorem

  The theorem should have roughly the following form
  ```
  (g : X → Y) (f : Y → Z) (hg : P g g') (hf : P f f') → P (f∘g) fg'
  ```
  and `gId`, `fId`, `hgId`, `hfId` are indices of corresponding arguments in the theorem `thmName`
   -/
  | comp (dataSynthName thrmName : Name) (gId fId hgId hfId : Nat)
  /-- Let binding theorem

  The theorem should have roughly the following form
  ```
  (g : X → Y) (f : Y → X → Z) (hg : P g g') (hf : P f f') → P (fun x => let y := g x; f y x) fg'
  ```
  and `gId`, `fId`, `hgId`, `hfId` are indices of corresponding arguments in the theorem `thmName`
  -/
  | letE (dataSynthName thrmName : Name) (gId fId hgId hfId : Nat)
  /-- Pi theorem

  The theorem should have roughly the following form
  ```
  (f : X → I → Y) (hf : ∀ i, P (f · i) (f' i)) → P (fun x i => f x i) f'
  ```
  and `fId`, `hfId` are indices of corresponding arguments in the theorem `thmName`
  -/
  | pi   (dataSynthName thrmName : Name) (fId hfId : Nat)
  /-- Constant theorem

  The theorem should have roughly the following form
  ```
  (y : Y) → P (fun x => y) c'
  `` -/
  | const (dataSynthName thrmName : Name)
  /-- Projection theorem

  This theorem says that if we can restrict `f : X → Y` to a smaller domain `X₁` and we know how
  to transform this restriction then we know how to transform `f`.

  The theorem should have roughly the following form
  ```
  (f : X → Y) (g : X₁ → Y) (p₁ : X → X₁) (p₂ : X → X₂) (q : X₁ → X₂ → X) (hg : P g g') → P f f'
  ```

  TODO: There has to be some condition on p₁,p₂,q that they really form a decomposition.
  -/
  | proj (dataSynthName thrmName : Name) (fId gId p₁Id p₂Id qId hgId : Nat)
  deriving Inhabited

inductive LambdaTheoremType where | comp | letE | pi | const | proj
  deriving BEq, Inhabited, Hashable

/-- Get name of the theorem. -/
def LambdaTheorem.thmName (thm : LambdaTheorem) : Name :=
  match thm with
  | .comp _ thmName _ _ _ _ => thmName
  | .letE _ thmName _ _ _ _ => thmName
  | .pi   _ thmName _ _     => thmName
  | .const _ thmName        => thmName
  | .proj _ thmName _ _ _ _ _ _ => thmName

/-- Get name of the data synthesis. -/
def LambdaTheorem.dataSynthName (thm : LambdaTheorem) : Name :=
  match thm with
  | .comp dataSynthName _ _ _ _ _ => dataSynthName
  | .letE dataSynthName _ _ _ _ _ => dataSynthName
  | .pi   dataSynthName _ _ _     => dataSynthName
  | .const dataSynthName _        => dataSynthName
  | .proj dataSynthName _ _ _ _ _ _ _ => dataSynthName

/-- Get proof of a theorem. -/
def LambdaTheorem.getProof (thm : LambdaTheorem) : MetaM Expr :=
  match thm with
  | .comp _ thmName _ _ _ _ => mkConstWithFreshMVarLevels thmName
  | .letE _ thmName _ _ _ _ => mkConstWithFreshMVarLevels thmName
  | .pi   _ thmName _ _     => mkConstWithFreshMVarLevels thmName
  | .const _ thmName        => mkConstWithFreshMVarLevels thmName
  | .proj _ thmName _ _ _ _ _ _ => mkConstWithFreshMVarLevels thmName

/-- Get type of the theorem. -/
def LambdaTheorem.type (thm : LambdaTheorem) : LambdaTheoremType :=
  match thm with
  | .comp .. => LambdaTheoremType.comp
  | .letE .. => LambdaTheoremType.letE
  | .pi   .. => LambdaTheoremType.pi
  | .const .. => LambdaTheoremType.const
  | .proj .. => LambdaTheoremType.proj

/-- Enviroment extension for lambda theorems -/
initialize lambdaTheoremsExt : SimpleScopedEnvExtension LambdaTheorem (Std.HashMap (Name×LambdaTheoremType) (Array LambdaTheorem)) ←
  registerSimpleScopedEnvExtension {
    name     := by exact decl_name%
    initial  := {}
    addEntry := fun d e => d.alter (e.dataSynthName,e.type)
      (fun v? => match v? with | .some v => v.push e | .none => #[e])
  }

/-- Add lambda theorem to the enviroment. -/
def addLambdaTheorem (thm : LambdaTheorem) : CoreM Unit :=
  lambdaTheoremsExt.add thm

/-- Add lambda theorem to the enviroment. -/
def getLambdaTheorems (dataSynthName : Name) (thmType : LambdaTheoremType) :
    CoreM (Array LambdaTheorem) := do
  return (lambdaTheoremsExt.getState (← getEnv))[(dataSynthName,thmType)]?.getD #[]


----------------------------------------------------------------------------------------------------

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
  let keys ← RefinedDiscrTree.mkDTExprs b false

  trace[Meta.Tactic.data_synth]
    "dataSynth: {dataSynthDecl.name}\
   \nthmName: {declName}\
   \nkeys: {keys}"


  let thm : DataSynthTheorem := {
    name := dataSynthDecl.name
    thmName := declName
    keys    := keys
    priority  := prio
  }
  return thm


def addTheorem (declName : Name) (kind : AttributeKind := .global) (prio : Nat := eval_prio default) : MetaM Unit := do


  let thm ← getTheoremFromConst declName prio

  dataSynthTheoremsExt.add thm kind
