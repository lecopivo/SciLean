import Lean.Meta.Tactic.Simp.Types

import Std.Data.RBMap.Alter

import SciLean.Prelude
import SciLean.Lean.MergeMapDeclarationExtension
 
open Lean Meta.Simp

namespace SciLean.FTrans


-- Tracing --
-------------
initialize registerTraceClass `Meta.Tactic.ftrans
initialize registerTraceClass `Meta.Tactic.ftrans.step
-- initialize registerTraceClass `Meta.Tactic.ftrans.missing_rule
-- initialize registerTraceClass `Meta.Tactic.ftrans.normalize_let
initialize registerTraceClass `Meta.Tactic.ftrans.rewrite
-- initialize registerTraceClass `Meta.Tactic.ftrans.lambda_special_cases


/-- Simp attribute to mark function transformation rules.
-/
register_simp_attr ftrans_simp

macro "ftrans" : attr => `(attr| ftrans_simp ↓)

/-- 
Function Transformation Info
--

Stores information and custom functionalities for a function transformation.
-/
structure Info where
  getFTransFun? (expr : Expr) : Option Expr
  replaceFTransFun (expr : Expr) (newFun : Expr) : Expr
  applyLambdaLetRule    (expr : Expr) : SimpM (Option Step)
  applyLambdaLambdaRule (expr : Expr) : SimpM (Option Step)
  -- The CoreM monad is likely completely unecessary
  -- I just do not know how to convert `(tactic| by simp) into Syntax without
  -- having some kind of monad
  discharger : Expr → SimpM (Option Expr)

deriving Inhabited

private def Info.merge! (ftrans : Name) (_ _ : Info) : Info :=
panic! 
s!"Two conflicting definitions for function transformation `{ftrans}` found!

  Keep only one and remove the other."

initialize FTransExt : MergeMapDeclarationExtension Info 
  ← mkMergeMapDeclarationExtension ⟨Info.merge!, sorry_proof⟩


/-- 
  Returns function transformation name and function being tranformed if `e` is function tranformation expression.
 -/
def getFTrans? (e : Expr) : CoreM (Option (Name × Info × Expr)) := do
  let .some ftransName := e.getAppFn.constName?
    | return none

  let .some info ← FTransExt.find? ftransName
    | return none

  let .some f := info.getFTransFun? e
    | return none

  return (ftransName, info, f)

/-- 
  Returns function transformation info if `e` is function tranformation expression.
 -/
def getFTransInfo? (e : Expr) : CoreM (Option Info) := do
  let .some (_, info, _) ← getFTrans? e
    | return none
  return info

/-- 
  Returns function transformation info if `e` is function btranformation expression.
 -/
def getFTransFun? (e : Expr) : CoreM (Option Expr) := do
  let .some (_, _, f) ← getFTrans? e
    | return none
  return f



--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

initialize registerTraceClass `trace.Tactic.ftrans.new_property

local instance : Ord Name := ⟨Name.quickCmp⟩
/-- 
This holds a collection of property theorems for a fixed constant
-/
def FTransRules := Std.RBMap Name (Std.RBSet Name compare /- maybe (Std.RBSet SimTheorem ...) -/) compare

namespace FTransRules

  instance : Inhabited FTransRules := by unfold FTransRules; infer_instance
  instance : ToString FTransRules := ⟨fun s => toString (s.toList.map fun (n,r) => (n,r.toList))⟩

  variable (fp : FTransRules)

  def insert (property : Name) (thrm : Name) : FTransRules := 
    fp.alter property (λ p? =>
      match p? with
      | some p => some (p.insert thrm)
      | none => some (Std.RBSet.empty.insert thrm))

  def empty : FTransRules := Std.RBMap.empty

end FTransRules

private def FTransRules.merge! (function : Name) (fp fp' : FTransRules) :  FTransRules :=
  fp.mergeWith (t₂ := fp') λ _ p q => p.union q

initialize FTransRulesExt : MergeMapDeclarationExtension FTransRules 
  ← mkMergeMapDeclarationExtension ⟨FTransRules.merge!, sorry_proof⟩

open Lean Qq Meta Elab Term in
initialize funTransRuleAttr : TagAttribute ← 
  registerTagAttribute 
    `ftrans_rule
    "Attribute to tag the basic rules for a function transformation." 
    (validate := fun ruleName => do
      let env ← getEnv 
      let .some ruleInfo := env.find? ruleName 
        | throwError s!"Can't find a constant named `{ruleName}`!"

      let rule := ruleInfo.type

      MetaM.run' do
        forallTelescope rule λ _ eq => do

          let .some (_,lhs,rhs) := eq.app3? ``Eq
            | throwError s!"`{← ppExpr eq}` is not a rewrite rule!"

          let .some (transName, transInfo, f) ← getFTrans? lhs
            | throwError s!
"`{← ppExpr eq}` is not a rewrite rule of known function transformaion!
To register function transformation call:
```
#eval show Lean.CoreM Unit from do
  FTrans.FTransExt.insert <name> <info>
```
where <name> is name of the function transformation and <info> is corresponding `FTrans.Info`. 
"
          let .some funName := 
              match f with 
              | .app f _ => f.getAppFn.constName?
              | .lam _ _ b _ => b.getAppFn.constName?
              | _ => none
            | throwError "Function being transformed is in invalid form!"

          FTransRulesExt.insert funName (FTransRules.empty.insert transName ruleName)
      )           

open Meta in
def getFTransRules (funName ftransName : Name) : CoreM (Array SimpTheorem) := do

  let .some rules ← FTransRulesExt.find? funName
    | return #[]

  let .some rules := rules.find? ftransName
    | return #[]

  let env ← getEnv

  let rules : List SimpTheorem ← rules.toList.mapM fun r => do
    let .some info := env.find? r
      | panic! "hihi"
    
    return { 
      proof  := info.value!
      origin := .decl r
      rfl    := false 
    }

  return rules.toArray

  
