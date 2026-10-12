module

public import SciLean.Logic.Function.Bijective

public import SciLean.Tactic.FunTrans.Attr
public import SciLean.Tactic.FunTrans.Elab

@[expose] public section


set_option linter.unusedVariables false

set_option deprecated.oldSectionVars true

variable
  {X : Type _} [Nonempty X]
  {Y : Type _} [Nonempty Y]
  {Z : Type _} [Nonempty Z]
  {X₁ : Type _} [Nonempty X₁]
  {X₂ : Type _} [Nonempty X₂]

open Function

/-- If `F` is bijective and `G` is its right inverse then `G` is the inverse of `F`. -/
private theorem invFun_of_rightInverse {X Y : Type _} [Nonempty X] {F : X → Y} {G : Y → X}
    (hF : Bijective F) (h : ∀ y, F (G y) = y) : invFun F = G :=
  Function.invFun_eq_of_injective_of_rightInverse hF.injective h

namespace Function.invFun

attribute [fun_trans] Function.invFun

-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem id_rule
  : invFun (fun (x : X) => x)
    =
    fun x => x := by
  apply Function.invFun_comp
  exact Function.injective_id

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
  invFun_of_rightInverse (hf.comp hg) fun z => by
    rw [Function.invFun_eq (hg.surjective _), Function.invFun_eq (hf.surjective _)]

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
  invFun_of_rightInverse
    (hf.comp (((Equiv.prodComm Y X₂).bijective.comp (hg.prodMap bijective_id)).comp hp))
    fun z => by
    have h := Function.invFun_eq (hp.surjective
      (invFun g (invFun (fun xy : X₂×Y => f xy.1 xy.2) z).2,
       (invFun (fun xy : X₂×Y => f xy.1 xy.2) z).1))
    simp only [Prod.mk.injEq] at h
    simp only [h.1, h.2, Function.invFun_eq (hg.surjective _)]
    exact Function.invFun_eq (hf.surjective z)

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
  invFun_of_rightInverse (by fun_prop) fun yz => by
    have h := Function.invFun_eq (hp.surjective (invFun f yz.1, invFun g yz.2))
    simp only [Prod.mk.injEq] at h
    simp only [h.1, h.2, Function.invFun_eq (hf.surjective _),
      Function.invFun_eq (hg.surjective _)]



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
  := invFun_of_rightInverse (by fun_prop) fun y => by
    rw [Function.invFun_eq (hf.surjective _), neg_neg]


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
  := invFun_of_rightInverse (by fun_prop) fun y => by
    rw [Function.invFun_eq (hf.surjective _), inv_inv]


@[fun_trans]
theorem Inv.inv.arg_a0.invFun_rule_field
  [Field Y]
  (f : X → Y) (hf : Bijective f) (hf' : ∀ x, f x ≠ 0)
  : invFun (fun x => (f x)⁻¹)
    =
    fun y =>
      invFun f (y⁻¹)
  := invFun_of_rightInverse ((Equiv.inv Y).bijective.comp hf) fun y => by
    rw [Function.invFun_eq (hf.surjective _), inv_inv]


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
  := invFun_of_rightInverse (by fun_prop) fun y' => by
    rw [Function.invFun_eq (hf.surjective _), sub_add_cancel]

@[fun_trans]
theorem HAdd.hAdd.arg_a1.invFun_rule
  [AddGroup Y]
  (y : Y)  (f : X → Y) (hf : Bijective f)
  : invFun (fun x => y + f x)
    =
    fun y' =>
      invFun f (-y + y')
  := invFun_of_rightInverse (by fun_prop) fun y' => by
    rw [Function.invFun_eq (hf.surjective _), add_neg_cancel_left]


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
  := invFun_of_rightInverse (by fun_prop) fun y' => by
    rw [Function.invFun_eq (hf.surjective _), add_sub_cancel_right]


-- note: this holds only if addition on `Y` commutes, in a general `AddGroup`
--       the inverse is `fun y' => invFun f (-y' + y)`, hence `AddCommGroup Y` is assumed here
@[fun_trans]
theorem HSub.hSub.arg_a1.invFun_rule
  [AddCommGroup Y]
   (y : Y) (f : X → Y) (hf : Bijective f)
  : invFun (fun x => y - f x )
    =
    fun y' =>
      invFun f (y - y')
  := invFun_of_rightInverse (by fun_prop) fun y' => by
    rw [Function.invFun_eq (hf.surjective _), sub_sub_cancel]



-- HMul.hMul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HMul.hMul.arg_a0.invFun_rule_group
  [Group Y]
  (f : X → Y) (y : Y) (hf : Bijective f)
  : invFun (fun x => f x * y)
    =
    fun y' =>
      invFun f (y' / y)
  := invFun_of_rightInverse (by fun_prop) fun y' => by
    rw [Function.invFun_eq (hf.surjective _), div_mul_cancel]

@[fun_trans]
theorem HMul.hMul.arg_a1.invFun_rule_group
  [Group Y]
  (y : Y) (f : X → Y) (hf : Bijective f)
  : invFun (fun x => y * f x)
    =
    fun y' =>
      invFun f (y⁻¹ * y')
  := invFun_of_rightInverse (by fun_prop) fun y' => by
    rw [Function.invFun_eq (hf.surjective _), mul_inv_cancel_left]

@[fun_trans]
theorem HMul.hMul.arg_a0.invFun_rule_field
  [Field Y]
  (f : X → Y) (y : Y) (hf : Bijective f) (hy : y ≠ 0)
  : invFun (fun x => f x * y)
    =
    fun y' =>
      invFun f (y'/y)
  := invFun_of_rightInverse ((Equiv.mulRight₀ y hy).bijective.comp hf) fun y' => by
    rw [Function.invFun_eq (hf.surjective _), div_mul_cancel₀ _ hy]

@[fun_trans]
theorem HMul.hMul.arg_a1.invFun_rule_field
  [Field Y]
  (y : Y) (f : X → Y) (hf : Bijective f) (hy : y ≠ 0)
  : invFun (fun x => y * f x)
    =
    fun y' =>
      invFun f (y⁻¹ * y')
  := invFun_of_rightInverse ((Equiv.mulLeft₀ y hy).bijective.comp hf) fun y' => by
    rw [Function.invFun_eq (hf.surjective _), mul_inv_cancel_left₀ hy]


-- SMul.sMul -------------------------------------------------------------------
--------------------------------------------------------------------------------


@[fun_trans]
theorem HSMul.hSMul.arg_a1.invFun_rule_group
  [Group G] [MulAction G Y]
  (g : G) (f : X → Y) (hf : Bijective f)
  : invFun (fun x => g • f x)
    =
    fun y =>
      invFun f (g⁻¹ • y)
  := invFun_of_rightInverse (by fun_prop) fun y => by
    rw [Function.invFun_eq (hf.surjective _), smul_inv_smul]


@[fun_trans]
theorem HSMul.hSMul.arg_a1.invFun_rule_field
  [Field R] [MulAction R Y]
  (r : R) (f : X → Y) (hf : Bijective f) (hr : r ≠ 0)
  : invFun (fun x => r • f x)
    =
    fun y =>
      invFun f (r⁻¹ • y)
  := invFun_of_rightInverse
      (Function.Bijective.HSMul.hSMul.arg_a1.Bijective_rule_field r f hf hr) fun y => by
    rw [Function.invFun_eq (hf.surjective _), smul_smul, mul_inv_cancel₀ hr, one_smul]


-- VAdd.vAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------


@[fun_trans]
theorem HVAdd.hVAdd.arg_a1.invFun_rule_group
  [AddGroup G] [AddAction G Y]
  (g : G) (f : X → Y) (hf : Bijective f)
  : invFun (fun x => g +ᵥ f x)
    =
    fun y =>
      invFun f (-g +ᵥ y)
  := invFun_of_rightInverse (by fun_prop) fun y => by
    rw [Function.invFun_eq (hf.surjective _), vadd_vadd, add_neg_cancel, zero_vadd]


-- Equiv.toFun/invFun ----------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Equiv.toFun.arg_a0.invFun_rule (f : Y ≃ Z) (g : X → Y) (hf : Bijective g)
  : Function.invFun (fun x => f (g x))
    =
    fun z => Function.invFun g (f.invFun z) :=
  invFun_of_rightInverse (f.bijective.comp hf) fun z => by
    rw [Function.invFun_eq (hf.surjective _)]
    exact f.apply_symm_apply z

@[fun_trans]
theorem Equiv.invFun.arg_a0.invFun_rule (f : Y ≃ Z) (g : X → Z) (hf : Bijective g)
  : Function.invFun (fun x => f.invFun (g x))
    =
    fun z => Function.invFun g (f z) :=
  invFun_of_rightInverse (f.symm.bijective.comp hf) fun z => by
    rw [Function.invFun_eq (hf.surjective _)]
    exact f.symm_apply_apply z
