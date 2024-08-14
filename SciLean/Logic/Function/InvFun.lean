import SciLean.Logic.Function.Bijective

import SciLean.Tactic.FunTrans.Attr
import SciLean.Tactic.FunTrans.Elab

set_option linter.unusedVariables false

set_option deprecated.oldSectionVars true

variable
  {X : Type _} [Nonempty X]
  {Y : Type _} [Nonempty Y]
  {Z : Type _} [Nonempty Z]
  {X₁ : Type _} [Nonempty X₁]
  {X₂ : Type _} [Nonempty X₂]

open Function

namespace Function.invFun

attribute [fun_trans] Function.invFun

-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem id_rule
  : invFun (fun (x : X) => x)
    =
    fun x => x := by sorry_proof

@[fun_trans]
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

-- @[fun_trans]
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

@[fun_trans]
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



-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
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

@[fun_trans]
theorem Inv.inv.arg_a0.invFun_rule_group
  [Group Y]
  (f : X → Y) (hf : Bijective f)
  : invFun (fun x => (f x)⁻¹)
    =
    fun y =>
      invFun f (y⁻¹)
  := by sorry_proof


@[fun_trans]
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

@[fun_trans]
theorem HAdd.hAdd.arg_a0.invFun_rule
  [AddGroup Y]
  (f : X → Y) (y : Y) (hf : Bijective f)
  : invFun (fun x => f x + y)
    =
    fun y' =>
      invFun f (y' - y)
  := by sorry_proof

@[fun_trans]
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

@[fun_trans]
theorem HSub.hSub.arg_a0.invFun_rule
  [AddGroup Y]
  (f : X → Y) (y : Y) (hf : Bijective f)
  : invFun (fun x => f x - y)
    =
    fun y' =>
      invFun f (y' + y)
  := by sorry_proof


@[fun_trans]
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

@[fun_trans]
def HMul.hMul.arg_a0.invFun_rule_group
  [Group Y]
  (f : X → Y) (y : Y) (hf : Bijective f)
  : invFun (fun x => f x * y)
    =
    fun y' =>
      invFun f (y' / y)
  := by sorry_proof

@[fun_trans]
def HMul.hMul.arg_a1.invFun_rule_group
  [Group Y]
  (y : Y) (f : X → Y) (hf : Bijective f)
  : invFun (fun x => y * f x)
    =
    fun y' =>
      invFun f (y⁻¹ * y')
  := by sorry_proof

@[fun_trans]
def HMul.hMul.arg_a0.invFun_rule_field
  [Field Y]
  (f : X → Y) (y : Y) (hf : Bijective f) (hy : y ≠ 0)
  : invFun (fun x => f x * y)
    =
    fun y' =>
      invFun f (y'/y)
  := by sorry_proof

@[fun_trans]
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


@[fun_trans]
def HSMul.hSMul.arg_a1.invFun_rule_group
  [Group G] [MulAction G Y]
  (g : G) (f : X → Y) (hf : Bijective f)
  : invFun (fun x => g • f x)
    =
    fun y =>
      invFun f (g⁻¹ • y)
  := by sorry_proof


@[fun_trans]
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


@[fun_trans]
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

@[fun_trans]
theorem Equiv.toFun.arg_a0.invFun_rule (f : Y ≃ Z) (g : X → Y) (hf : Bijective g)
  : Function.invFun (fun x => f (g x))
    =
    fun z => Function.invFun g (f.invFun z) :=
by
  sorry_proof

@[fun_trans]
theorem Equiv.invFun.arg_a0.invFun_rule (f : Y ≃ Z) (g : X → Z) (hf : Bijective g)
  : Function.invFun (fun x => f.invFun (g x))
    =
    fun z => Function.invFun g (f z) :=
by
  sorry_proof
