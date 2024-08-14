import Mathlib.Algebra.Field.Defs
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic.FunProp

import SciLean.Util.SorryProof

set_option linter.unusedVariables false

-- Some missing theorems -------------------------------------------------------
--------------------------------------------------------------------------------

theorem Function.invFun_comp' [Nonempty α] {f : α → β} (hf : f.Injective) {x : α} :
    f.invFun (f x) = x := by
  suffices (f.invFun ∘ f) x = x by assumption
  rw[Function.invFun_comp hf]
  rfl


-- Basic rules -----------------------------------------------------------------
--------------------------------------------------------------------------------

open Function

namespace Function.Bijective

set_option deprecated.oldSectionVars true

variable
  {X : Type _} [Nonempty X]
  {Y : Type _} [Nonempty Y]
  {Z : Type _} [Nonempty Z]

attribute [fun_prop] Bijective

@[fun_prop]
theorem id_rule
  : Bijective (fun x : X => x)
  := bijective_id

@[fun_prop]
theorem comp_rule
  (f : Y → Z) (g : X → Y)
  (hf : Bijective f) (hg : Bijective g)
  : Bijective (fun x => f (g x))
  := Bijective.comp hf hg


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

@[fun_prop]
theorem Prod.mk.arg_fstsnd.Bijective_rule_simple
  : Bijective (fun xy : X×Y => (xy.1, xy.2))
  := by sorry_proof

@[fun_prop]
theorem Prod.mk.arg_fstsnd.Bijective_rule_simple'
  : Bijective (fun xy : X×Y => (xy.2, xy.1))
  := by sorry_proof


@[fun_prop]
theorem Prod.mk.arg_fstsnd.Bijective_rule
  (f : X₁ → Y) (g : X₂ → Z) (p₁ : X → X₁) (p₂ : X → X₂)
  (hf : Bijective f) (hg : Bijective g) (hp : Bijective (fun x => (p₁ x, p₂ x)))
  : Bijective (fun x : X => (f (p₁ x), g (p₂ x)))
  := by sorry_proof




-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Neg.neg.arg_a0.Bijective_rule
  [AddGroup Y]
  (f : X → Y) (hf : Bijective f)
  : Bijective fun x => - f x
  := by sorry_proof


-- Inv.inv ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Inv.inv.arg_a0.Bijective_rule_group
  [Group Y]
  (f : X → Y) (hf : Bijective f)
  : Bijective fun x => (f x)⁻¹
  := by sorry_proof


@[fun_prop]
theorem Inv.inv.arg_a0.Bijective_rule_field
  [Field Y]
  (f : X → Y) (hf : Bijective f) (hf' : ∀ x, f x ≠ 0)
  : Bijective fun x => (f x)⁻¹
  := by sorry_proof


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HAdd.hAdd.arg_a0.Bijective_rule
  [AddGroup Y]
  (f : X → Y) (y : Y) (hf : Bijective f)
  : Bijective fun x => f x + y
  := by sorry_proof

@[fun_prop]
theorem HAdd.hAdd.arg_a1.Bijective_rule
  [AddGroup Y]
  (y : Y)  (f : X → Y) (hf : Bijective f)
  : Bijective fun x => y + f x
  := by sorry_proof


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HSub.hSub.arg_a0.Bijective_rule
  [AddGroup Y]
  (f : X → Y) (y : Y) (hf : Bijective f)
  : Bijective fun x => f x - y
  := by sorry_proof


@[fun_prop]
theorem HSub.hSub.arg_a1.Bijective_rule
  [AddGroup Y]
   (y : Y) (f : X → Y) (hf : Bijective f)
  : Bijective fun x => y - f x
  := by sorry_proof



-- HMul.hMul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HMul.hMul.arg_a0.Bijective_rule_group
  [Group Y]
  (f : X → Y) (y : Y) (hf : Bijective f)
  : Bijective (fun x => f x * y)
  := by sorry_proof

@[fun_prop]
theorem HMul.hMul.arg_a1.Bijective_rule_group
  [Group Y]
  (y : Y) (f : X → Y) (hf : Bijective f)
  : Bijective (fun x => y * f x)
  := by sorry_proof

@[fun_prop]
theorem HMul.hMul.arg_a0.Bijective_rule_field
  [Field Y]
  (f : X → Y) (y : Y) (hf : Bijective f) (hy : y ≠ 0)
  : Bijective (fun x => f x * y)
  := by sorry_proof

@[fun_prop]
theorem HMul.hMul.arg_a1.Bijective_rule_field
  [Field Y]
  (y : Y) (f : X → Y) (hf : Bijective f) (hy : y ≠ 0)
  : Bijective (fun x => y * f x)
  := by sorry_proof



-- SMul.sMul -------------------------------------------------------------------
--------------------------------------------------------------------------------


@[fun_prop]
theorem HSMul.hSMul.arg_a1.Bijective_rule_group
  [Group G] [MulAction G Y]
  (g : G) (f : X → Y) (hf : Bijective f)
  : Bijective (fun x => g • f x)
  := by sorry_proof


@[fun_prop]
theorem HSMul.hSMul.arg_a1.Bijective_rule_field
  [Field R] [MulAction R Y]
  (r : R) (f : X → Y) (hf : Bijective f) (hr : r ≠ 0)
  : Bijective (fun x => r • f x)
  := by sorry_proof


-- VAdd.vAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------


@[fun_prop]
theorem HVAdd.hVAdd.arg_a1.Bijective_rule_group
  [AddGroup G] [AddAction G Y]
  (g : G) (f : X → Y) (hf : Bijective f)
  : Bijective (fun x => g +ᵥ f x)
  := by sorry_proof



-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HDiv.hDiv.arg_a0.Bijective_rule_group
  [Group Y]
  (f : X → Y) (y : Y)
  (hf : Bijective f)
  : Bijective (fun x => f x / y) :=
by
  sorry_proof

@[fun_prop]
theorem HDiv.hDiv.arg_a0.Bijective_rule_field
  [Field Y]
  (f : X → Y) (y : Y)
  (hf : Bijective f) (hy : y ≠ 0)
  : Bijective (fun x => f x / y) :=
by
  sorry_proof


-- Equiv.toFun/invFun ----------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Equiv.toFun.arg_a0.Bijective_rule (f : Y ≃ Z) (g : X → Y) (hf : Bijective g)
  : Bijective (fun x => f (g x)) :=
by
  sorry_proof

@[fun_prop]
theorem Equiv.invFun.arg_a0.Bijective_rule (f : Y ≃ Z) (g : X → Z) (hf : Bijective g)
  : Bijective (fun x => f.invFun (g x)) :=
by
  sorry_proof
