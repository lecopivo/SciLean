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
register_simp_attr ftrans


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
  discharger : TSyntax `tactic

deriving Inhabited

private def merge! (ftrans : Name) (_ _ : Info) : Info :=
panic! 
s!"Two conflicting definitions for function transformation `{ftrans}` found!

  Keep only one and remove the other."

initialize infoExt : MergeMapDeclarationExtension Info 
  ← mkMergeMapDeclarationExtension ⟨merge!, sorry_proof⟩
