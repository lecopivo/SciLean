import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Prod
import Mathlib.LinearAlgebra.Prod
import SciLean.Core.Objects.FinVec

import SciLean.Tactic.FProp.Basic
import SciLean.Tactic.FProp.Notation

set_option linter.unusedVariables false

--------------------------------------------------------------------------------
open LeanColls
namespace IsLinearMap

attribute [fun_prop] IsLinearMap

section Semiring

variable {R X Y Z ι : Type _} {E : ι → Type _}
  [Semiring R]
  [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y]
  [AddCommGroup Z] [Module R Z]
  [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)]

@[fun_prop]
theorem isLinearMap_id : IsLinearMap R (fun x : X ↦ x) := LinearMap.id.isLinear

-- todo: I think this does not get used at all
@[fun_prop]
theorem isLinearMap_const_zero
  : IsLinearMap R (fun _ : X => (0 : Y))
  := by sorry_proof

@[fun_prop]
theorem isLinearMap_comp {f : Y → Z} {g : X → Y}
    (hf : IsLinearMap R f) (hg : IsLinearMap R g) : IsLinearMap R (fun x ↦ f (g x)) :=
  ((mk' _ hf).comp (mk' _ hg)).isLinear

@[fun_prop]
theorem isLinearMap_apply (i : ι) : IsLinearMap R (fun f : (i : ι) → E i ↦ f i) := by sorry_proof

@[fun_prop]
theorem isLinearMap_pi (f : X → (i : ι) → E i) (hf : ∀ i, IsLinearMap R (f · i)) :
    IsLinearMap R (fun x i ↦ f x i) := by sorry_proof

end Semiring

section CommSemiring

variable {R X Y Z ι : Type _} {E : ι → Type _}
  [CommSemiring R]
  [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y]
  [AddCommGroup Z] [Module R Z]
  [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)]

@[fun_prop]
theorem mk'.arg_f.IsLinearMap_rule (f : X → Y → Z)
    (hf₁ : ∀ y, IsLinearMap R (f · y)) (hf₂ : ∀ x, IsLinearMap R (f x ·)) :
    IsLinearMap R (fun x => mk' (f x) (hf₂ x)) := sorry_proof

@[fun_prop]
theorem LinearMap_coe.apply_right (f : X → Y →ₗ[R] Z) (y : Y) (hf : IsLinearMap R f) :
    IsLinearMap R (fun x => (f x) y) := sorry_proof

@[fun_prop]
theorem LinearMap_coe.apply_left (f : Y →ₗ[R] Z) (g : X → Y) (hg : IsLinearMap R g) :
    IsLinearMap R (fun x => f (g x)) := sorry_proof

end CommSemiring



section Semiring
variable {R X Y Z ι : Type _} {E : ι → Type _}
  [Semiring R]
  [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y]
  [AddCommGroup Z] [Module R Z]
  [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
  [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]

theorem by_linear_map {f : X → Y} (g : X →ₗ[R] Y) (h : ∀ x, f x = g x) :
    IsLinearMap R f := sorry_proof


-- Prod.mk ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.mk.arg_fstsnd.IsLinearMap_rule
  (f : X → Z) (g : X → Y)
  (hf : IsLinearMap R f) (hg : IsLinearMap R g)
  : IsLinearMap R fun x => (g x, f x) := by_linear_map ((mk' _ hg).prod (mk' _ hf)) (by simp)


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.fst.arg_self.IsLinearMap_rule
    (f : X → Y×Z) (hf : IsLinearMap R f) : IsLinearMap R fun (x : X) => (f x).fst :=
  by_linear_map ((LinearMap.fst _ _ _).comp (mk' _ hf)) (by simp)


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.snd.arg_self.IsLinearMap_rule
    (f : X → Y×Z) (hf : IsLinearMap R f) : IsLinearMap R fun (x : X) => (f x).snd :=
  by_linear_map ((LinearMap.snd _ _ _).comp (mk' _ hf)) (by simp)


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Neg.neg.arg_a0.IsLinearMap_rule
    (f : X → Y) (hf : IsLinearMap R f) : IsLinearMap R fun x => - f x :=
  by_linear_map (- (mk' _ hf)) (by simp)


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HAdd.hAdd.arg_a0a1.IsLinearMap_rule
    (f g : X → Y) (hf : IsLinearMap R f) (hg : IsLinearMap R g) :
    IsLinearMap R fun x => f x + g x :=
  by_linear_map ((mk' _ hf) + (mk' _ hg)) (by simp)



-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HSub.hSub.arg_a0a1.IsLinearMap_rule
    (f g : X → Y) (hf : IsLinearMap R f) (hg : IsLinearMap R g) :
    IsLinearMap R fun x => f x - g x :=
  by_linear_map ((mk' _ hf) - (mk' _ hg)) (by simp)

-- Smul.smul ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HSMul.hSMul.arg_a0.IsLinearMap_rule
    (f : X → R) (y : Y) (hf : IsLinearMap R f) : IsLinearMap R fun x => f x • y :=
  let a : R →ₗ[R] Y := mk' _ (isLinearMap_smul' y)
  let b := (mk' _ hf)
  by_linear_map (a.comp b) (by simp)

@[fun_prop]
theorem HSMul.hSMul.arg_a1.IsLinearMap_rule_nat
    (c : ℕ) (f : X → Y) (hf : IsLinearMap R f) : IsLinearMap R fun x => c • f x :=
  sorry_proof

@[fun_prop]
theorem HSMul.hSMul.arg_a1.IsLinearMap_rule_int
    (c : ℤ) (f : X → Y) (hf : IsLinearMap R f) : IsLinearMap R fun x => c • f x :=
  sorry_proof

-- IndexType.sum ----------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem IndexType.sum.arg_f.IsLinearMap_rule
  (f : X → ι → Y) (hf : ∀ i, IsLinearMap R (f · i))
  : IsLinearMap R fun x => ∑ i, f x i := by sorry_proof


-- d/ite -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem ite.arg_te.IsLinearMap_rule
  (c : Prop) [dec : Decidable c]
  (t e : X → Y) (ht : IsLinearMap R t) (he : IsLinearMap R e)
  : IsLinearMap R fun x => ite c (t x) (e x) :=
by
  induction dec
  case isTrue h  => simp[h]; fun_prop
  case isFalse h => simp[h]; fun_prop


@[fun_prop]
theorem dite.arg_te.IsLinearMap_rule
  (c : Prop) [dec : Decidable c]
  (t : c  → X → Y) (ht : ∀ p, IsLinearMap R (t p))
  (e : ¬c → X → Y) (he : ∀ p, IsLinearMap R (e p))
  : IsLinearMap R fun x => dite c (t · x) (e · x) :=
by
  induction dec
  case isTrue h  => simp[h]; apply ht
  case isFalse h => simp[h]; apply he



end Semiring

-- HMul.hMul ---------------------------------------------------------------------
--------------------------------------------------------------------------------

section CommSemiring

variable {R X Y Z ι : Type _} {E : ι → Type _}
  [CommSemiring R]
  [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y]
  [AddCommGroup Z] [Module R Z]
  [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]

@[fun_prop]
theorem HSMul.hSMul.arg_a1.IsLinearMap_rule
    (c : R) (f : X → Y) (hf : IsLinearMap R f) : IsLinearMap R fun x => c • f x :=
  let a : Y →ₗ[R] Y := mk' _ (isLinearMap_smul c)
  let b := (mk' _ hf)
  by_linear_map (a.comp b) (by simp)


@[fun_prop]
theorem HMul.hMul.arg_a0.IsLinearMap_rule
    (f : X → R) (hf : IsLinearMap R f) (y' : R) : IsLinearMap R fun x => f x * y' :=
  let a : R →ₗ[R] R := mk' _ (isLinearMap_smul' y')
  let b := (mk' _ hf)
  let c := a.comp b
  sorry_proof
  -- by_linear_map c sorry


@[fun_prop]
theorem HMul.hMul.arg_a1.IsLinearMap_rule
  (f : X → R) (hf : IsLinearMap R f) (y' : R) : IsLinearMap R fun x => y' * f x :=
  let a : R →ₗ[R] R := mk' _ (isLinearMap_smul y')
  let b := (mk' _ hf)
  let c := a.comp b
  sorry_proof
  -- by_linear_map c sorry


end CommSemiring
end IsLinearMap

open LeanColls
namespace SciLean
section OnFinVec

variable
  {K : Type _} [IsROrC K]
  {IX : Type} [IndexType IX] [LawfulIndexType IX] [DecidableEq IX] {X : Type _} [FinVec IX K X]
  {IY : Type} [IndexType IY] [LawfulIndexType IY] [DecidableEq IY] {Y : Type _} [FinVec IY K Y]
  {IZ : Type} [IndexType IZ] [LawfulIndexType IZ] [DecidableEq IZ] {Z : Type _} [FinVec IZ K Z]

@[fun_prop]
theorem Basis.proj.arg_x.IsLinearMap_rule (i : IX) :
    IsLinearMap K (fun x : X => ℼ i x) := by sorry_proof

@[fun_prop]
theorem DualBasis.dualProj.arg_x.IsLinearMap_rule (i : IX) :
    IsLinearMap K (fun x : X => ℼ' i x) := by sorry_proof

@[fun_prop]
theorem BasisDuality.toDual.arg_x.IsLinearMap_rule :
    IsLinearMap K (fun x : X => BasisDuality.toDual x) := by sorry_proof

@[fun_prop]
theorem BasisDuality.fromDual.arg_x.IsLinearMap_rule :
    IsLinearMap K (fun x : X => BasisDuality.fromDual x) := by sorry_proof

end OnFinVec
end SciLean
