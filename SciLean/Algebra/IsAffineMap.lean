import Mathlib.Algebra.Module.LinearMap.Basic
import SciLean.Algebra.IsLinearMap

set_option linter.unusedVariables false

open SciLean

--------------------------------------------------------------------------------

variable {R X Y Z ι : Type _} {E : ι → Type _}
  [CommRing R]
  [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y]
  [AddCommGroup Z] [Module R Z]
  [IndexType ι] [DecidableEq ι]
  [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]

variable (R)
-- poor man's version of affine map
-- todo: align with mathlib more in particular it should be defined ove affine space rather then
--       over module
@[fun_prop]
structure IsAffineMap (f : X → Y) : Prop where
  is_affine : IsLinearMap R (fun x => f x - f 0)

variable {R}

namespace IsAffineMap

attribute [fun_prop] IsAffineMap

@[fun_prop]
theorem IsAffineMap_id : IsAffineMap R (fun x : X ↦ x) := by constructor; simp; fun_prop

@[fun_prop]
theorem IsAffineMap_const (y : Y)
  : IsAffineMap R (fun _ : X => y)
  := by constructor; simp; apply IsLinearMap.isLinearMap_const_zero

@[fun_prop]
theorem IsAffineMap_comp {f : Y → Z} {g : X → Y}
    (hf : IsAffineMap R f) (hg : IsAffineMap R g) : IsAffineMap R (fun x ↦ f (g x)) := by
  sorry_proof

@[fun_prop]
theorem IsAffineMap_apply (i : ι) : IsAffineMap R (fun f : (i : ι) → E i ↦ f i) := by sorry_proof

@[fun_prop]
theorem IsAffineMap_pi (f : X → (i : ι) → E i) (hf : ∀ i, IsAffineMap R (f · i)) :
    IsAffineMap R (fun x i ↦ f x i) := sorry_proof


-- @[fun_prop]
-- theorem mk'.arg_f.IsAffineMap_rule (f : X → Y → Z)
--     (hf₁ : ∀ y, IsAffineMap R (f · y)) (hf₂ : ∀ x, IsAffineMap R (f x ·)) :
--     IsAffineMap R (fun x => mk' (f x) (hf₂ x)) := sorry_proof

-- @[fun_prop]
-- theorem LinearMap_coe.apply_right (f : X → Y →ₗ[R] Z) (y : Y) (hf : IsAffineMap R f) :
--     IsAffineMap R (fun x => (f x) y) := sorry_proof

-- @[fun_prop]
-- theorem LinearMap_coe.apply_left (f : Y →ₗ[R] Z) (g : X → Y) (hg : IsAffineMap R g) :
--     IsAffineMap R (fun x => f (g x)) := sorry_proof


end IsAffineMap
open IsAffineMap

-- todo: change to by_affine_map
-- theorem by_linear_map {f : X → Y} (g : X →ₗ[R] Y) (h : ∀ x, f x = g x) :
--     IsAffineMap R f := sorry_proof


-- Prod.mk ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.mk.arg_fstsnd.IsAffineMap_rule
  (f : X → Z) (g : X → Y)
  (hf : IsAffineMap R f) (hg : IsAffineMap R g)
  : IsAffineMap R fun x => (g x, f x) := sorry_proof


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.fst.arg_self.IsAffineMap_rule
    (f : X → Y×Z) (hf : IsAffineMap R f) : IsAffineMap R fun (x : X) => (f x).fst :=
  sorry_proof


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.snd.arg_self.IsAffineMap_rule
    (f : X → Y×Z) (hf : IsAffineMap R f) : IsAffineMap R fun (x : X) => (f x).snd :=
  sorry_proof


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Neg.neg.arg_a0.IsAffineMap_rule
    (f : X → Y) (hf : IsAffineMap R f) : IsAffineMap R fun x => - f x :=
  sorry_proof


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HAdd.hAdd.arg_a0a1.IsAffineMap_rule
    (f g : X → Y) (hf : IsAffineMap R f) (hg : IsAffineMap R g) :
    IsAffineMap R fun x => f x + g x := sorry_proof



-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HSub.hSub.arg_a0a1.IsAffineMap_rule
    (f g : X → Y) (hf : IsAffineMap R f) (hg : IsAffineMap R g) :
    IsAffineMap R fun x => f x - g x := sorry_proof

-- Smul.smul ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HSMul.hSMul.arg_a0.IsAffineMap_rule
    (f : X → R) (y : Y) (hf : IsAffineMap R f) : IsAffineMap R fun x => f x • y := sorry_proof

@[fun_prop]
theorem HSMul.hSMul.arg_a1.IsAffineMap_rule
    (c : R) (f : X → Y) (hf : IsAffineMap R f) : IsAffineMap R fun x => c • f x := sorry_proof

@[fun_prop]
theorem HSMul.hSMul.arg_a1.IsAffineMap_rule' {S} [CommRing S] [Module S X] [Module S Y] [SMul S R] [IsScalarTower S R Y]
    (c : R) (f : X → Y) (hf : IsAffineMap R f) : IsAffineMap S fun x => c • f x := sorry_proof


@[fun_prop]
theorem HSMul.hSMul.arg_a1.IsAffineMap_rule_nat
    (c : ℕ) (f : X → Y) (hf : IsAffineMap R f) : IsAffineMap R fun x => c • f x := sorry_proof

@[fun_prop]
theorem HSMul.hSMul.arg_a1.IsAffineMap_rule_int
    (c : ℤ) (f : X → Y) (hf : IsAffineMap R f) : IsAffineMap R fun x => c • f x := sorry_proof

-- HMul.hMul ------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HMul.hMul.arg_a0.IsAffineMap_rule
    (f : X → R) (hf : IsAffineMap R f) (y' : R) : IsAffineMap R fun x => f x * y' := sorry_proof

@[fun_prop]
theorem HMul.hMul.arg_a1.IsAffineMap_rule
  (f : X → R) (hf : IsAffineMap R f) (y' : R) : IsAffineMap R fun x => y' * f x := sorry_proof


-- IndexType.sum ----------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem IndexType.sum.arg_f.IsAffineMap_rule
  (f : X → ι → Y) (hf : ∀ i, IsAffineMap R (f · i))
  : IsAffineMap R fun x => ∑ i, f x i := by sorry_proof


-- d/ite -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem ite.arg_te.IsAffineMap_rule
  (c : Prop) [dec : Decidable c]
  (t e : X → Y) (ht : IsAffineMap R t) (he : IsAffineMap R e)
  : IsAffineMap R fun x => ite c (t x) (e x) :=
by
  induction dec
  case isTrue h  => simp[h]; fun_prop
  case isFalse h => simp[h]; fun_prop


@[fun_prop]
theorem dite.arg_te.IsAffineMap_rule
  (c : Prop) [dec : Decidable c]
  (t : c  → X → Y) (ht : ∀ p, IsAffineMap R (t p))
  (e : ¬c → X → Y) (he : ∀ p, IsAffineMap R (e p))
  : IsAffineMap R fun x => dite c (t · x) (e · x) :=
by
  induction dec
  case isTrue h  => simp[h]; apply ht
  case isFalse h => simp[h]; apply he


namespace SciLean
section OnFinVec

variable
  {K : Type _} [RCLike K]
  {IX : Type} [IndexType IX] [DecidableEq IX] {X : Type _} [FinVec IX K X]
  {IY : Type} [IndexType IY] [DecidableEq IY] {Y : Type _} [FinVec IY K Y]
  {IZ : Type} [IndexType IZ] [DecidableEq IZ] {Z : Type _} [FinVec IZ K Z]

@[fun_prop]
theorem Basis.proj.arg_x.IsAffineMap_rule (i : IX) :
    IsAffineMap K (fun x : X => ℼ i x) := by sorry_proof

@[fun_prop]
theorem DualBasis.dualProj.arg_x.IsAffineMap_rule (i : IX) :
    IsAffineMap K (fun x : X => ℼ' i x) := by sorry_proof

@[fun_prop]
theorem BasisDuality.toDual.arg_x.IsAffineMap_rule :
    IsAffineMap K (fun x : X => BasisDuality.toDual x) := by sorry_proof

@[fun_prop]
theorem BasisDuality.fromDual.arg_x.IsAffineMap_rule :
    IsAffineMap K (fun x : X => BasisDuality.fromDual x) := by sorry_proof

end OnFinVec
end SciLean
