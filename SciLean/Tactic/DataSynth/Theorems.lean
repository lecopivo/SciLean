import Lean
import Mathlib.Lean.Meta.RefinedDiscrTree

import SciLean.Tactic.DataSynth.Decl
import SciLean.Lean.Meta.Basic

open Lean Meta
open Mathlib.Meta.FunProp

namespace SciLean.Tactic.DataSynth

structure Theorem where
  dataSynthName : Name
  thmName : Name
deriving Inhabited, BEq, Hashable

/-- Get proof of a theorem. -/
def Theorem.getProof (thm : Theorem) : MetaM Expr := do
  mkConstWithFreshMVarLevels thm.thmName


inductive LambdaTheoremData where
  /-- Composition theorem

  The theorem should have roughly the following form
  ```
  (g : X → Y) (f : Y → Z) (hg : P g g') (hf : P f f') → P (f∘g) fg'
  ```
  and `gId`, `fId`, `hgId`, `hfId` are indices of corresponding arguments in the theorem `thmName`
   -/
  | comp (gId fId hgId hfId : Nat)
  /-- Let binding theorem

  The theorem should have roughly the following form
  ```
  (g : X → Y) (f : Y → X → Z) (hg : P g g') (hf : P f f') → P (fun x => let y := g x; f y x) fg'
  ```
  and `gId`, `fId`, `hgId`, `hfId` are indices of corresponding arguments in the theorem `thmName`
  -/
  | letE (gId fId hgId hfId : Nat)
  /-- Let binding theorem where we skip let binding

  This theorem can be used on functions like `fun x => let y := let n := ⌊x⌋; x + n` which is
  differentiable everywhere except integers.

  The theorem should have roughly the following form
  ```
  (g : X → Y) (f : Y → X → Z) (hf : ∀ y, P (f y) (f' y)) → P (fun x => let y := g x; f y x) fg'
  ```
  and `gId`, `fId`,  `hfId` are indices of corresponding arguments in the theorem `thmName`
  -/
  | letSkip (gId fId hfId : Nat)
  /-- Pi theorem

  The theorem should have roughly the following form
  ```
  (f : X → I → Y) (hf : ∀ i, P (f · i) (f' i)) → P (fun x i => f x i) f'
  ```
  and `fId`, `hfId` are indices of corresponding arguments in the theorem `thmName`
  -/
  | pi (fId hfId : Nat)
  /-- Constant theorem

  The theorem should have roughly the following form
  ```
  (y : Y) → P (fun x => y) c'
  `` -/
  | const
  /-- Projection theorem

  This theorem says that if we can restrict `f : X → Y` to a smaller domain `X₁` and we know how
  to transform this restriction then we know how to transform `f`.

  The theorem should have roughly the following form
  ```
  (f : X → Y) (g : X₁ → Y) (p₁ : X → X₁) (p₂ : X → X₂) (q : X₁ → X₂ → X) (hg : P g g') → P f f'
  ```

  TODO: There has to be some condition on p₁,p₂,q that they really form a decomposition.
  -/
  | proj (fId gId p₁Id p₂Id qId hgId /- hdec -/ : Nat)
  deriving Inhabited, BEq, Hashable

inductive LambdaTheoremType where | comp | letE | letSkip | pi | const | proj
  deriving BEq, Inhabited, Hashable

structure LambdaTheorem extends Theorem where
  data : LambdaTheoremData
  deriving BEq, Inhabited, Hashable

/-- Get proof of a theorem. -/
def LambdaTheorem.getProof (thm : LambdaTheorem) : MetaM Expr :=
  thm.toTheorem.getProof

/-- Returns hints that should be applied before and after unification in `tryTheorem?` -/
def LambdaTheorem.getHint (thm : LambdaTheorem) (args : Array Expr) :
    MetaM (Array (Nat×Expr) × Array (Nat×Expr)) :=
  match thm.data with
  | .comp gId fId hgId hfId =>
    if h : args.size = 4 then
      return (#[(gId,args[0]),(fId,args[1])],#[(hgId,args[2]),(hfId,args[3])])
    else
      throwError "comp theorem expects 4 arguments"
  | .letE gId fId hgId hfId =>
    if h : args.size = 4 then
      return (#[(gId,args[0]),(fId,args[1])],#[(hgId,args[2]),(hfId,args[3])])
    else
      throwError "letE theorem expects 4 arguments"
  | .letSkip gId fId hfId =>
    if h : args.size = 3 then
      return (#[(gId,args[0]),(fId,args[1])],#[(hfId,args[2])])
    else
      throwError "letSkip theorem expects 3 arguments"
  | .pi fId hfId =>
    if h : args.size = 2 then
      return (#[(fId,args[0])],#[(hfId,args[1])])
    else
      throwError "pi theorem expects 2 arguments"
  | .const =>
    if h : args.size = 0 then
      return (#[],#[])
    else
      throwError "const theorem expects 1 argument"
  | .proj fId gId p₁Id p₂Id qId hgId =>
    if h : args.size = 6 then
      return (#[(fId,args[0]),(gId,args[1]),(p₁Id,args[2]),(p₂Id,args[3]),(qId,args[4])],#[(hgId,args[5])])
    else
      throwError "proj theorem expects 6 arguments"

/-- Get type of the theorem. -/
def LambdaTheorem.type (thm : LambdaTheorem) : LambdaTheoremType :=
  match thm.data with
  | .comp .. => LambdaTheoremType.comp
  | .letE .. => LambdaTheoremType.letE
  | .letSkip .. => LambdaTheoremType.letSkip
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
structure GeneralTheorem extends Theorem where
  /-- discrimination tree keys used to index this theorem -/
  keys        : List RefinedDiscrTree.DTExpr
  /-- priority -/
  priority    : Nat  := eval_prio default
  deriving Inhabited, BEq



/-- Get proof of a theorem. -/
def DataSynthTheorem.getProof (thm : GeneralTheorem) : MetaM Expr := do
  mkConstWithFreshMVarLevels thm.thmName


open Mathlib.Meta.FunProp in
/-- -/
structure DataSynthTheorems where
  /-- -/
  theorems     : RefinedDiscrTree GeneralTheorem := {}
  deriving Inhabited

/-- -/
abbrev DataSynthTheoremsExt := SimpleScopedEnvExtension GeneralTheorem DataSynthTheorems


open Mathlib.Meta.FunProp in
/-- -/
initialize dataSynthTheoremsExt : DataSynthTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name     := by exact decl_name%
    initial  := {}
    addEntry := fun d e =>
      {d with theorems := e.keys.foldl (RefinedDiscrTree.insertDTExpr · · e) d.theorems}
  }



def getTheoremFromConst (declName : Name) (prio : Nat := eval_prio default) : MetaM GeneralTheorem := do
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


  let thm : GeneralTheorem := {
    dataSynthName := dataSynthDecl.name
    thmName := declName
    keys    := keys
    priority  := prio
  }
  return thm


def addTheorem (declName : Name) (kind : AttributeKind := .global) (prio : Nat := eval_prio default) : MetaM Unit := do

  let thm ← getTheoremFromConst declName prio

  dataSynthTheoremsExt.add thm kind
