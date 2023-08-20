import Mathlib.Algebra.Field.Defs
import Mathlib.GroupTheory.GroupAction.Defs

import SciLean.Tactic.FProp.Basic
import SciLean.Tactic.FProp.Notation

set_option linter.unusedVariables false

-- Basic rules -----------------------------------------------------------------
--------------------------------------------------------------------------------

open Function

namespace Function.Bijective

variable 
  {X : Type _} [Nonempty X]
  {Y : Type _} [Nonempty Y]
  {Z : Type _} [Nonempty Z]
  

theorem id_rule
  : Bijective (fun x : X => x)
  := bijective_id
  

theorem comp_rule
  (f : Y → Z) (g : X → Y) 
  (hf : Bijective f) (hg : Bijective g)
  : Bijective (fun x => f (g x))
  := Bijective.comp hf hg


--------------------------------------------------------------------------------
-- Register Bijective ----------------------------------------------------------
--------------------------------------------------------------------------------

open Lean Meta SciLean FProp
def Bijective.fpropExt : FPropExt where
  fpropName := ``Bijective
  getFPropFun? e := 
    if e.isAppOf ``Bijective then
      if let .some f := e.getArg? 2 then
        some f
      else 
        none
    else
      none

  replaceFPropFun e f := 
    if e.isAppOf ``Bijective then
      e.modifyArg (fun _ => f) 2
    else          
      e

  identityRule e :=
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``id_rule 
      origin := .decl ``id_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  constantRule _ := return none

  compRule e f g := do
    let thm : SimpTheorem :=
    {
      proof  := ← mkAppM ``comp_rule #[f,g]
      origin := .decl ``comp_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  lambdaLetRule _ _ _ := return none
  lambdaLambdaRule _ _ := return none
  projRule _ := return none

  discharger e := 
    FProp.tacticToDischarge (Syntax.mkLit ``Lean.Parser.Tactic.assumption "assumption") e

-- register fderiv
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FProp.fpropExt.addEntry env (``Bijective, Bijective.fpropExt))


end Function.Bijective


variable 
  {X : Type _} [Nonempty X]
  {X₁ : Type _} [Nonempty X₁]
  {X₂ : Type _} [Nonempty X₂]
  {Y : Type _} [Nonempty Y]
  {Z : Type _} [Nonempty Z]


-- Prod ------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- Prod.mk --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.mk.arg_fstsnd.Bijective_rule_simple
  : Bijective (fun xy : X×Y => (xy.1, xy.2))
  := by sorry_proof

@[fprop]
theorem Prod.mk.arg_fstsnd.Bijective_rule_simple'
  : Bijective (fun xy : X×Y => (xy.2, xy.1))
  := by sorry_proof


@[fprop]
theorem Prod.mk.arg_fstsnd.Bijective_rule
  (f : X₁ → Y) (g : X₂ → Z) (p₁ : X → X₁) (p₂ : X → X₂)
  (hf : Bijective f) (hg : Bijective g) (hp : Bijective (fun x => (p₁ x, p₂ x)))
  : Bijective (fun x : X => (f (p₁ x), g (p₂ x)))
  := by sorry_proof


-- Id --------------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem id.arg_a.Bijective_rule
  : Bijective (id : X → X) := by unfold id; fprop


-- Function.comp ---------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Function.comp.arg_a0.Bijective_rule
  (f : Y → Z) (hf : Bijective f)
  (g : X → Y) (hg : Bijective g)
  : Bijective (f ∘ g)
  := Bijective.comp hf hg



-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Neg.neg.arg_a0.Bijective_rule
  [AddGroup Y]
  (f : X → Y) (hf : Bijective f) 
  : Bijective fun x => - f x 
  := by sorry_proof


-- Inv.inv ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Inv.inv.arg_a0.Bijective_rule_group
  [Group Y]
  (f : X → Y) (hf : Bijective f) 
  : Bijective fun x => (f x)⁻¹
  := by sorry_proof


@[fprop]
theorem Inv.inv.arg_a0.Bijective_rule_field
  [Field Y]
  (f : X → Y) (hf : Bijective f) (hf' : ∀ x, f x ≠ 0)
  : Bijective fun x => (f x)⁻¹
  := by sorry_proof


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem HAdd.hAdd.arg_a0.Bijective_rule
  [AddGroup Y]
  (f : X → Y) (y : Y) (hf : Bijective f) 
  : Bijective fun x => f x + y
  := by sorry_proof

@[fprop]
theorem HAdd.hAdd.arg_a1.Bijective_rule
  [AddGroup Y]
  (y : Y)  (f : X → Y) (hf : Bijective f) 
  : Bijective fun x => y + f x
  := by sorry_proof


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem HSub.hSub.arg_a0.Bijective_rule
  [AddGroup Y]
  (f : X → Y) (y : Y) (hf : Bijective f) 
  : Bijective fun x => f x - y
  := by sorry_proof


@[fprop]
theorem HSub.hSub.arg_a1.Bijective_rule
  [AddGroup Y]
   (y : Y) (f : X → Y) (hf : Bijective f) 
  : Bijective fun x => y - f x 
  := by sorry_proof



-- HMul.hMul -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HMul.hMul.arg_a0.Bijective_rule_group
  [Group Y]
  (f : X → Y) (y : Y) (hf : Bijective f)
  : Bijective (fun x => f x * y)
  := by sorry_proof

@[fprop]
def HMul.hMul.arg_a1.Bijective_rule_group
  [Group Y]
  (y : Y) (f : X → Y) (hf : Bijective f)
  : Bijective (fun x => y * f x)
  := by sorry_proof

@[fprop]
def HMul.hMul.arg_a0.Bijective_rule_field
  [Field Y]
  (f : X → Y) (y : Y) (hf : Bijective f) (hy : y ≠ 0)
  : Bijective (fun x => f x * y)
  := by sorry_proof

@[fprop]
def HMul.hMul.arg_a1.Bijective_rule_field
  [Field Y]
  (y : Y) (f : X → Y) (hf : Bijective f) (hy : y ≠ 0)
  : Bijective (fun x => y * f x)
  := by sorry_proof



-- SMul.sMul -------------------------------------------------------------------
-------------------------------------------------------------------------------- 


@[fprop]
def HSMul.hSMul.arg_a1.Bijective_rule_group
  [Group G] [MulAction G Y]
  (g : G) (f : X → Y) (hf : Bijective f)
  : Bijective (fun x => g • f x)
  := by sorry_proof


@[fprop]
def HSMul.hSMul.arg_a1.Bijective_rule_field
  [Field R] [MulAction R Y]
  (r : R) (f : X → Y) (hf : Bijective f) (hr : r ≠ 0)
  : Bijective (fun x => r • f x)
  := by sorry_proof



-- HDiv.hDiv -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HDiv.hDiv.arg_a0.Bijective_rule_group
  [Group Y]
  (f : X → Y) (y : Y)
  (hf : Bijective f)
  : Bijective (fun x => f x / y) := 
by 
  sorry_proof

@[fprop]
def HDiv.hDiv.arg_a0.Bijective_rule_field
  [Field Y]
  (f : X → Y) (y : Y)
  (hf : Bijective f) (hy : y ≠ 0)
  : Bijective (fun x => f x / y) := 
by 
  sorry_proof
