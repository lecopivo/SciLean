import SciLean.Core.FunctionPropositions.Bijective

import SciLean.Tactic.FTrans.Basic

set_option linter.unusedVariables false

variable 
  {X : Type _} [Nonempty X]
  {Y : Type _} [Nonempty Y]
  {Z : Type _} [Nonempty Z]
  {X₁ : Type _} [Nonempty X₁]
  {X₂ : Type _} [Nonempty X₂]

open Function

namespace Function.invFun

-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

variable (X)
theorem id_rule 
  : invFun (fun (x : X) => x) 
    = 
    fun x => x := by sorry_proof

variable {X}

theorem comp_rule 
  (f : Y → Z) (g : X → Y) 
  (hf : Bijective f) (hg : Bijective g)
  : invFun (fun x => f (g x))
    =
    fun z =>
      let y := invFun f z
      let x := invFun g y
      x := 
by sorry_proof


theorem let_rule 
  (f : X₂ → Y → Z) (g : X₁ → Y) (p₁ : X → X₁) (p₂ : X → X₂)
  (hf : Bijective (fun xy : X₂×Y => f xy.1 xy.2)) (hg : Bijective g) (hp : Bijective (fun x => (p₁ x, p₂ x)))
  : invFun (fun x => let y := g (p₁ x); f (p₂ x) y)
    =
    fun z =>
      let x₂y := invFun (fun xy : X₂×Y => f xy.1 xy.2) z
      let x₁ := invFun g x₂y.2
      let x := invFun (fun x => (p₁ x, p₂ x)) (x₁,x₂y.1)
      x := 
by sorry_proof


-- Register `adjoint` as function transformation -------------------------------
--------------------------------------------------------------------------------

open Lean Meta Qq SciLean

def discharger (e : Expr) : SimpM (Option Expr) := do
  withTraceNode `fwdDeriv_discharger (fun _ => return s!"discharge {← ppExpr e}") do
  let cache := (← get).cache
  let config : FProp.Config := {}
  let state  : FProp.State := { cache := cache }
  let (proof?, state) ← FProp.fprop e |>.run config |>.run state
  _root_.modify (fun simpState => { simpState with cache := state.cache })
  if proof?.isSome then
    return proof?
  else
    -- if `fprop` fails try assumption
    let tac := FTrans.tacticToDischarge (Syntax.mkLit ``Lean.Parser.Tactic.assumption "assumption")
    let proof? ← tac e
    return proof?

open Lean Elab Term FTrans
def ftransExt : FTransExt where
  ftransName := ``invFun

  getFTransFun? e := 
    if e.isAppOf ``invFun then

      if let .some f := e.getArg? 3 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``invFun then
      e.setArg 3 f
    else          
      e

  idRule  e X := do
    tryTheorems
      #[ { proof := ← mkAppM ``id_rule #[X], origin := .decl ``id_rule, rfl := false} ]
      discharger e

  constRule _ _ _ := return none
  projRule _ _ _ := return none

  compRule e f g := do
    tryTheorems
      #[ { proof := ← 
             mkAppM ``comp_rule #[f, g], origin := .decl ``comp_rule, rfl := false} ]
      discharger e

  letRule e f g := return none
  piRule  e f := return none

  discharger := discharger


-- register adjoint
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``invFun, ftransExt))

end Function.invFun

--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

open SciLean Function

variable 
  {X : Type _} [Nonempty X]
  {Y : Type _} [Nonempty Y]
  {Z : Type _} [Nonempty Z]

open SciLean


-- Prod ------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- Prod.mk --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.mk.arg_fstsnd.invFun_rule
  (f : X₁ → Y) (g : X₂ → Z) (p₁ : X → X₁) (p₂ : X → X₂)
  (hf : Bijective f) (hg : Bijective g) (hp : Bijective (fun x => (p₁ x, p₂ x)))
  : invFun (fun x : X => (f (p₁ x), g (p₂ x)))
    =
    fun yz =>
      let x₁ := invFun f yz.1
      let x₂ := invFun g yz.2
      let x  := invFun (fun x => (p₁ x, p₂ x)) (x₁,x₂) 
      x := 
by sorry_proof


-- Id --------------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem id.arg_a.invFun_rule
  : invFun (fun x : X => id x)
    = 
    id := by unfold id; ftrans


-- Function.comp ---------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Function.comp.arg_a0.invFun_rule
  (f : Y → Z) (g : X → Y)
  (hf : Bijective f) (hg : Bijective g)
  : invFun (fun x => (f ∘ g) x)
    = 
    invFun g ∘ invFun f
  := by unfold Function.comp; ftrans



-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Neg.neg.arg_a0.invFun_rule
  [AddGroup Y]
  (f : X → Y) (hf : Bijective f) 
  : invFun (fun x => - f x)
    =
    fun y =>
      invFun f (-y)
  := by sorry_proof


-- Inv.inv ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Inv.inv.arg_a0.invFun_rule_group
  [Group Y]
  (f : X → Y) (hf : Bijective f) 
  : invFun (fun x => (f x)⁻¹)
    =
    fun y => 
      invFun f (y⁻¹)
  := by sorry_proof


@[ftrans]
theorem Inv.inv.arg_a0.invFun_rule_field
  [Field Y]
  (f : X → Y) (hf : Bijective f) (hf' : ∀ x, f x ≠ 0)
  : invFun (fun x => (f x)⁻¹)
    =
    fun y => 
      invFun f (y⁻¹)
  := by sorry_proof


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HAdd.hAdd.arg_a0.invFun_rule
  [AddGroup Y]
  (f : X → Y) (y : Y) (hf : Bijective f) 
  : invFun (fun x => f x + y)
    =
    fun y' => 
      invFun f (y' - y)
  := by sorry_proof

@[ftrans]
theorem HAdd.hAdd.arg_a1.invFun_rule
  [AddGroup Y]
  (y : Y)  (f : X → Y) (hf : Bijective f) 
  : invFun (fun x => y + f x)
    =
    fun y' => 
      invFun f (-y + y')
  := by sorry_proof


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSub.hSub.arg_a0.invFun_rule
  [AddGroup Y]
  (f : X → Y) (y : Y) (hf : Bijective f) 
  : invFun (fun x => f x - y)
    =
    fun y' =>
      invFun f (y' + y)
  := by sorry_proof


@[ftrans]
theorem HSub.hSub.arg_a1.invFun_rule
  [AddGroup Y]
   (y : Y) (f : X → Y) (hf : Bijective f) 
  : invFun (fun x => y - f x )
    =
    fun y' =>
      invFun f (y - y')
  := by sorry_proof



-- HMul.hMul -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans]
def HMul.hMul.arg_a0.invFun_rule_group
  [Group Y]
  (f : X → Y) (y : Y) (hf : Bijective f)
  : invFun (fun x => f x * y)
    =
    fun y' => 
      invFun f (y' / y)
  := by sorry_proof

@[ftrans]
def HMul.hMul.arg_a1.invFun_rule_group
  [Group Y]
  (y : Y) (f : X → Y) (hf : Bijective f)
  : invFun (fun x => y * f x)
    =
    fun y' => 
      invFun f (y⁻¹ * y')
  := by sorry_proof

@[ftrans]
def HMul.hMul.arg_a0.invFun_rule_field
  [Field Y]
  (f : X → Y) (y : Y) (hf : Bijective f) (hy : y ≠ 0)
  : invFun (fun x => f x * y)
    = 
    fun y' =>
      invFun f (y'/y)
  := by sorry_proof

@[ftrans]
def HMul.hMul.arg_a1.invFun_rule_field
  [Field Y]
  (y : Y) (f : X → Y) (hf : Bijective f) (hy : y ≠ 0)
  : invFun (fun x => y * f x)
    =
    fun y' =>
      invFun f (y⁻¹ * y')
  := by sorry_proof


-- SMul.sMul -------------------------------------------------------------------
-------------------------------------------------------------------------------- 


@[ftrans]
def HSMul.hSMul.arg_a1.invFun_rule_group
  [Group G] [MulAction G Y]
  (g : G) (f : X → Y) (hf : Bijective f)
  : invFun (fun x => g • f x)
    =
    fun y =>
      invFun f (g⁻¹ • y)
  := by sorry_proof


@[ftrans]
def HSMul.hSMul.arg_a1.invFun_rule_field
  [Field R] [MulAction R Y]
  (r : R) (f : X → Y) (hf : Bijective f) (hr : r ≠ 0)
  : invFun (fun x => r • f x)
    =
    fun y =>
      invFun f (r⁻¹ • y)
  := by sorry_proof


-- VAdd.vAdd -------------------------------------------------------------------
-------------------------------------------------------------------------------- 


@[ftrans]
def HVAdd.hVAdd.arg_a1.invFun_rule_group
  [AddGroup G] [AddAction G Y]
  (g : G) (f : X → Y) (hf : Bijective f)
  : invFun (fun x => g +ᵥ f x)
    =
    fun y =>
      invFun f (-g +ᵥ y)
  := by sorry_proof


-- Equiv.toFun/invFun ----------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Equiv.toFun.arg_a0.invFun_rule (f : Y ≃ Z) (g : X → Y) (hf : Bijective g)
  : Function.invFun (fun x => f.toFun (g x))
    =
    fun z => Function.invFun g (f.invFun z) := 
by
  sorry_proof

@[ftrans]
theorem Equiv.invFun.arg_a0.invFun_rule (f : Y ≃ Z) (g : X → Z) (hf : Bijective g)
  : Function.invFun (fun x => f.invFun (g x))
    =
    fun z => Function.invFun g (f.toFun z) := 
by
  sorry_proof
