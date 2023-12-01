import Qq
import Lean.Meta.Tactic.Simp.Types

import Std.Data.RBMap.Alter

import Mathlib.Data.FunLike.Basic

-- import SciLean.Prelude
import SciLean.Util.SorryProof
import SciLean.Lean.MergeMapDeclarationExtension
import SciLean.Lean.Meta.Basic
import SciLean.Lean.ToSSA
import SciLean.Tactic.StructuralInverse
import SciLean.Tactic.AnalyzeConstLambda

import SciLean.Data.Function
import SciLean.Data.ArraySet
 
open Lean Meta.Simp Qq

namespace SciLean.FTrans


-- Tracing --
-------------
initialize registerTraceClass `Meta.Tactic.ftrans
initialize registerTraceClass `Meta.Tactic.ftrans.step
initialize registerTraceClass `Meta.Tactic.ftrans.theorems
initialize registerTraceClass `Meta.Tactic.ftrans.missing_rule
-- initialize registerTraceClass `Meta.Tactic.ftrans.normalize_let
initialize registerTraceClass `Meta.Tactic.ftrans.rewrite
initialize registerTraceClass `Meta.Tactic.ftrans.discharge
initialize registerTraceClass `Meta.Tactic.ftrans.unify

initialize registerOption `linter.ftransDeclName { defValue := true, descr := "suggests declaration name for ftrans rule" }
initialize registerOption `linter.ftransSsaRhs { defValue := false, descr := "check if right hand side of ftrans rule is in single static asigment form" }
-- initialize registerTraceClass `Meta.Tactic.ftrans.lambda_special_cases

register_simp_attr ftrans_simp

open Meta Simp

/-- Data for `fun x i => f x (h i)` case when `h` is invertible
-/
structure PiInvData where
  {u v w w' : Level}
  {X : Q(Type u)}
  {Y : Q(Type v)}
  {I : Q(Type w)}
  {J : Q(Type w')}
  (f : Q($X → $J → $Y))
  (h  : Q($I → $J))
  (h' : Q($J → $I))
  (is_inverse : Q(Function.Inverse $h' $h))

/-- Data for `fun x i => f x (h i)` case when `h` admits left inverse/is surjective

The domain of `h` is decomposed into `I₁×I₂` and inverse `h'` between `I₂` and `J` is provided
-/
structure PiLInvData where
  -- {u v w u' v' w' : Level}
  {X Y I I₁ I₂ J : Q(Type)}
  (f : Q($X → $J → $Y))
  (h  : Q($I → $J))
  (h' : Q($I₁ → $J → $I₂))
  (p₁ : Q($I → $I₁))
  (p₂ : Q($I → $I₂))
  (q  : Q($I₁ → $I₂ → $I))
  (is_dec : Q(IsDecomposition $p₁ $p₂ $q))
  (is_inverse : Q(∀ i₁, Function.Inverse ($h' i₁) (fun i₂ => $h ($q i₁ i₂))))
  
structure FTransExt where
  /-- Function transformation name -/
  ftransName : Name
  /-- Get function being transformed from function transformation expression -/
  getFTransFun?    (expr : Expr) : Option Expr
  /-- Replace function being transformed in function transformation expression -/
  replaceFTransFun (expr : Expr) (newFun : Expr) : Expr
  /-- Custom rule for transforming `fun (x : X) => x` -/
  idRule      (expr X : Expr) : SimpM (Option Simp.Step)
  /-- Custom rule for transforming `fun (x : X)  => y` -/
  constRule   (expr X y : Expr) : SimpM (Option Simp.Step)
  /-- Custom rule for transforming `fun (x : (i' : ι) → X i') => x i` -/
  projRule    (expr X i : Expr) : SimpM (Option Simp.Step)
  /-- Custom rule for transforming `fun x => f (g x)` or `fun x => let y := g x; f y` -/
  compRule    (expr f g : Expr) : SimpM (Option Simp.Step)
  /-- Custom rule for transforming `fun x => let y := g x; f x y` -/
  letRule     (expr f g : Expr) : SimpM (Option Simp.Step)
  /-- Custom rule for transforming `fun x y => f x y` -/
  piRule      (expr f : Expr) : SimpM (Option Simp.Step) 

  useRefinedPiRules := false
  /-- Custom rule for transforming `fun (x : I → X) (i : I) => x i` -/
  piIdRule         (expr X I : Expr) : SimpM (Option Simp.Step) := return none
  /-- Custom rule for transforming `fun x (i : I) => f x` -/
  piConstRule      (expr f I : Expr) : SimpM (Option Simp.Step) := return none
  /-- Custom rule for transforming `fun x i j => f x i j` -/
  piUncurryRule    (expr f : Expr) : SimpM (Option Simp.Step) := return none
  /-- Custom rule for transforming `fun x (is : Is) => uncurryN n (f x) is` where `uncurryN n (f x)` has type `Is → Y` -/
  piCurryNRule    (expr f Is Y : Expr) (n : Nat) : SimpM (Option Simp.Step) := return none
  /-- Custom rule for transforming `fun x i => (f x i, g x i)` -/
  piProdRule    (expr f g : Expr) : SimpM (Option Simp.Step) := return none
  /-- Custom rule for transforming `fun x i => f (g x i) i` -/
  piCompRule       (expr f g : Expr) : SimpM (Option Simp.Step) := return none
  /-- Custom rule for transforming `fun x i => f (g x i) i` -/
  piElemWiseCompRule       (expr f g : Expr) : SimpM (Option Simp.Step) := return none
  /-- Custom rule for transforming `fun x i => let y := g x i; f x y i` -/
  piLetRule        (expr f g : Expr) : SimpM (Option Simp.Step) := return none
  /-- Custom rule for transforming `fun x i => f (g x i)` -/
  piSimpleCompRule (expr f g : Expr) : SimpM (Option Simp.Step) := return none
  /-- Custom rule for transforming `fun x i => f x (h i)` when `h` has inverse -/
  piInvRule  (expr f : Expr) (inv : FullInverse) : SimpM (Option Simp.Step) := return none
  /-- Custom rule for transforming `fun x i => f x (h i)` when `h` has left inverse  -/
  piRInvRule (expr f : Expr) (rinv : RightInverse) : SimpM (Option Simp.Step) := return none
  
  /-- Custom discharger for this function transformation -/
  discharger : Expr → SimpM (Option Expr)
  prodMk  := ``Prod.mk
  prodFst := ``Prod.fst
  prodSnd := ``Prod.snd
  /-- Name of this extension, keep the default value! -/
  name : Name := by exact decl_name%
deriving Inhabited


def mkFTransExt (n : Name) : ImportM FTransExt := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck FTransExt opts ``FTransExt n


initialize ftransExt : PersistentEnvExtension (Name × Name) (Name × FTransExt) (Std.RBMap Name FTransExt Name.quickCmp) ←
  registerPersistentEnvExtension {
    mkInitial := pure {}
    addImportedFn := fun s => do

      let mut r : Std.RBMap Name FTransExt Name.quickCmp := {}

      for s' in s do
        for (ftransName, extName) in s' do
          let ext ← mkFTransExt extName
          r := r.insert ftransName ext

      pure r
    addEntryFn := fun s (n, ext) => s.insert n ext
    exportEntriesFn := fun s => s.valuesArray.map (fun ext => (ext.ftransName, ext.name))
  }

/-- 
  Returns function transformation name and function being tranformed if `e` is function tranformation expression.
 -/
def getFTrans? (e : Expr) : CoreM (Option (Name × FTransExt × Expr)) := do

  let .some ftransName := 
      match e.getAppFn.constName? with
      | none => none
      | .some name => 
        if name != ``FunLike.coe then
          name
        else if let .some ftrans := e.getArg? 4 then
          ftrans.getAppFn.constName? 
        else
          none
    | return none

  let .some ext := (ftransExt.getState (← getEnv)).find? ftransName
    | return none

  let .some f := ext.getFTransFun? e
    | return none

  return (ftransName, ext, f)

/-- 
  Returns function transformation info if `e` is function tranformation expression.
 -/
def getFTransExt? (e : Expr) : CoreM (Option FTransExt) := do
  let .some (_, ext, _) ← getFTrans? e
    | return none
  return ext

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

structure FTransRule where
  -- ftransName : Name
  -- constName : Name
  ruleName : Name
  priority : Nat := 1000
  /-- Set of main argument indices in this rule
  For example:
   - rule `∂ (fun x => @HAdd.hAdd _ _ _ _ (f x) (g x)) = ...` has `mainIds = #[4,5]` 
   - rule `∂ (fun x => @HAdd.hAdd _ _ _ _ (f x) y) = ...` has `mainIds = #[4]` -/
  mainIds : ArraySet Nat
  /-- Set of trailing argument indices in this rule
  For example: 
  - rule `∂ (fun x i => @getElem _ _ _ _ _ (f x) i dom ` has `piArgs = #[6]`
  - rule `∂ (fun f x => @Function.invFun _ _ _ f x` has `piArgs = #[4]`
  - rule `∂ (fun x => (f x) + (g x)` has `piArgs = #[]`
  -/
  trailingIds : ArraySet Nat

def FTransRule.cmp (a b : FTransRule) : Ordering :=
  match a.trailingIds.lexOrd b.trailingIds with
  | .lt => .lt 
  | .gt => .gt 
  | .eq => 
    match a.mainIds.lexOrd b.mainIds with
    | .lt => .lt
    | .gt => .gt
    | .eq => 
      match compare a.priority b.priority with
      | .lt => .lt
      | .gt => .gt
      | .eq => a.ruleName.quickCmp b.ruleName

local instance : Ord Name := ⟨Name.quickCmp⟩
/-- 
This holds a collection of function transformation rules for a fixed constant
-/
def FTransRules := Std.RBMap Name (Std.RBSet FTransRule FTransRule.cmp) compare

namespace FTransRules

  instance : Inhabited FTransRules := by unfold FTransRules; infer_instance
  -- instance : ToString FTransRules := ⟨fun s => toString (s.toList.map fun (n,r) => (n,r.toList))⟩

  variable (fp : FTransRules)

  def insert (ftransName : Name) (rule : FTransRule) : FTransRules := 
    fp.alter ftransName (λ p? =>
      match p? with
      | some p => some (p.insert rule)
      | none => some (Std.RBSet.empty.insert rule))

  def empty : FTransRules := Std.RBMap.empty

end FTransRules

private def FTransRules.merge! (_ : Name) (fp fp' : FTransRules) :  FTransRules :=
  fp.mergeWith (t₂ := fp') λ _ p q => p.union q

initialize FTransRulesExt : MergeMapDeclarationExtension FTransRules 
  ← mkMergeMapDeclarationExtension ⟨FTransRules.merge!, sorry_proof⟩

open Lean Qq Meta Elab Term in
initialize funTransRuleAttr : TagAttribute ← 
  registerTagAttribute 
    `ftrans
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

          let .some (transName, _, f) ← getFTrans? lhs
            | throwError s!
"`{← ppExpr eq}` is not a rewrite rule of known function transformaion!
To register function transformation call:
```
#eval show Lean.CoreM Unit from do
  FTrans.FTransExt.insert <name> <info>
```
where <name> is name of the function transformation and <info> is corresponding `FTrans.Info`.
"

          if (← getBoolOption `linter.ftransSsaRhs) then
            let rhs' ← rhs.toSSA #[]
            if ¬(rhs.eqv rhs') then
              logWarning s!"right hand side is not in single static assigment form, expected form:\n{←ppExpr rhs'}"
          
          let data ← analyzeConstLambda f

          let suggestedRuleName :=
            data.constName 
              |>.append data.declSuffix
              |>.append (transName.getString.append "_rule")

          if (← getBoolOption `linter.ftransDeclName) &&
             ¬(suggestedRuleName.toString.isPrefixOf ruleName.toString) then
            logWarning s!"suggested name for this rule is {suggestedRuleName}"

          let ftransRule : FTransRule := {
            ruleName := ruleName
            mainIds := data.mainIds
            trailingIds := data.trailingIds
          }

          FTransRulesExt.insert data.constName (FTransRules.empty.insert transName ftransRule)
      )           


def getFTransRules (funName ftransName : Name) : CoreM (Array SimpTheorem) := do

  let .some rules ← FTransRulesExt.find? funName
    | return #[]

  let .some rules := rules.find? ftransName
    | return #[]

  let rules : List SimpTheorem ← rules.toList.filterMapM fun r => do
    -- if r.trailingIds.size ≠ 0 then
    --   return none
    -- else
      return .some {
        proof  := mkConst r.ruleName
        origin := .decl r.ruleName
        rfl    := false
      }

  return rules.toArray


def getFTransPiRules (funName ftransName : Name) : CoreM (Array SimpTheorem) := do

  let .some rules ← FTransRulesExt.find? funName
    | return #[]

  let .some rules := rules.find? ftransName
    | return #[]

  let rules : List SimpTheorem ← rules.toList.filterMapM fun r => do
    if r.trailingIds.size = 0 then
      return none
    else
      return .some {
        proof  := mkConst r.ruleName
        origin := .decl r.ruleName
        rfl    := false
      }

  return rules.toArray

  
