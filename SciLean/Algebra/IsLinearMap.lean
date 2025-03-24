import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Prod
import Mathlib.LinearAlgebra.Prod

import SciLean.Algebra.IsAddGroupHom
import SciLean.Analysis.Scalar.Basic
import SciLean.Analysis.Normed.Norm2
import SciLean.Meta.GenerateLinearMapSimp

set_option linter.unusedVariables false
set_option linter.hashCommand false

--------------------------------------------------------------------------------
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
theorem id_rule : IsLinearMap R (fun x : X ↦ x) := LinearMap.id.isLinear

-- todo: I think this does not get used at all
@[fun_prop]
theorem const_zero_rule
  : IsLinearMap R (fun _ : X => (0 : Y))
  := by constructor <;> simp

@[fun_prop]
theorem comp_rule {f : Y → Z} {g : X → Y}
    (hf : IsLinearMap R f) (hg : IsLinearMap R g) : IsLinearMap R (fun x ↦ f (g x)) :=
  ((mk' _ hf).comp (mk' _ hg)).isLinear

@[fun_prop]
theorem apply_rule (i : ι) : IsLinearMap R (fun f : (i : ι) → E i ↦ f i) := by constructor <;> simp

@[fun_prop]
theorem pi_rule (f : X → (i : ι) → E i) (hf : ∀ i, IsLinearMap R (f · i)) :
    IsLinearMap R (fun x i ↦ f x i) := by
  constructor
  · intros; funext i; simp[(hf i).1]
  · intros; funext i; simp[(hf i).2]

end Semiring

end IsLinearMap

----------------------------------------------------------------------------------------------------
-- Lambda notation ---------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section LinearMapMk'

variable {R X Y Z ι : Type _} {E : ι → Type _}
  [Semiring R]
  [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y]
  [AddCommGroup Z] [Module R Z]
  [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)]


variable (R)
def LinearMap.mk' (f : X → Y) (hf : IsLinearMap R f) : X →ₗ[R] Y := .mk (.mk f hf.1) hf.2
variable {R}

macro "fun " x:ident " =>ₗ[" R:term "] " b:term : term =>
  `(LinearMap.mk' $R (fun $x => $b) (by fun_prop))

macro "fun " x:ident " : " X:term " =>ₗ[" R:term "] " b:term : term =>
  `(LinearMap.mk' $R (fun ($x : $X) => $b) (by fun_prop))

macro "fun " "(" x:ident " : " X:term ")" " =>ₗ[" R:term "] " b:term : term =>
  `(LinearMap.mk' $R (fun ($x : $X) => $b) (by fun_prop))


@[simp, simp_core, simp_core ↓]
theorem LinearMap.mk'_eval (f : X → Y) (hf : IsLinearMap R f) (x : X) :
    mk' R f hf x = f x := by rfl

@[simp, simp_core, simp_core ↓]
theorem LinearMap.mk'_coe (f : X → Y) (hf : IsLinearMap R f) :
    mk' R f hf = f := by rfl

@[simp, simp_core, simp_core ↓]
theorem LinearMap.eta_reduce (f : X →ₗ[R] Y) :
    mk' R f.1 ⟨f.1.2,f.2⟩ = f := by rfl

@[app_unexpander LinearMap.mk'] def unexpandLinearMapMk : Lean.PrettyPrinter.Unexpander
  | `($(_) $R $f:term $_:term) =>
    match f with
    | `(fun $x':ident => $b:term) => `(fun $x' =>ₗ[$R] $b)
    | `(fun ($x':ident : $ty) => $b:term) => `(fun ($x' : $ty) =>ₗ[$R] $b)
    | `(fun $x':ident : $ty => $b:term) => `(fun $x' : $ty =>ₗ[$R] $b)
    | _  => `(fun x =>L[$R] $f x)
  | _  => throw ()


-- This theorem is necessary for `lsimp` tactic. Normal `simp` seems to have some fancy support
-- to perform congruence on functions like this automatically.
@[congr]
theorem LinearMap.mk'_congr
    (f g : X → Y) (hf : IsLinearMap R f) (h : f = g) :
    (fun x =>ₗ[R] f x) = LinearMap.mk' R g (by rw[← h]; apply hf) := by ext; simp_all

@[simp]
theorem LinearMap.mk'_zero  :
  LinearMap.mk' R (fun _ : X => (0 : Y)) (by fun_prop) = 0 := by rfl

end LinearMapMk'

namespace IsLinearMap
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
    IsLinearMap R (fun x => mk' (f x) (hf₂ x)) := by
  unfold IsLinearMap.mk'
  constructor
  · intro x y; ext y'; simp[(hf₁ y').1]
  · intro x y; ext y'; simp[(hf₁ y').2]

@[fun_prop]
theorem LinearMap_coe.apply_right (f : X → Y →ₗ[R] Z) (y : Y) (hf : IsLinearMap R f) :
    IsLinearMap R (fun x => (f x) y) := by constructor; simp[hf.1]; simp[hf.2]

@[fun_prop]
theorem LinearMap_coe.apply_left (f : Y →ₗ[R] Z) (g : X → Y) (hg : IsLinearMap R g) :
    IsLinearMap R (fun x => f (g x)) := by constructor; simp[hg.1]; simp[hg.2]

theorem restrictScalars {S} [Semiring S] [Algebra R S]
    {X : Type u_3} [AddCommGroup X] [Module R X] [Module S X] [IsScalarTower R S X]
    {Y : Type u_4} [AddCommGroup Y] [Module R Y] [Module S Y] [IsScalarTower R S Y]
    {f : X → Y} (h : IsLinearMap S f) : IsLinearMap R f := by
  constructor
  · apply h.map_add
  · intro c x
    calc _ = f (c • (1 • x)) := by simp
         _ = f ((c • (1:S)) • x) := by simp
         _ = (c • (1:S)) • f (x) := by apply h.map_smul
         _ = c • f x := by simp

end CommSemiring

end IsLinearMap
open IsLinearMap SciLean

section Semiring

set_option deprecated.oldSectionVars true

variable {R X Y Z ι : Type _} {E : ι → Type _}
  [Semiring R]
  [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y]
  [AddCommGroup Z] [Module R Z]
  -- [IndexType ι] [DecidableEq ι]
  [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]

theorem by_linear_map {f : X → Y} (g : X →ₗ[R] Y) (h : ∀ x, f x = g x) :
    IsLinearMap R f := by
  constructor
  intro x y; simp[h (x+y), h x, h y]
  intro c x; simp[h (c•x), h x]


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

theorem Prod.fst.arg_self.IsLinearMap_rule_simple :
    IsLinearMap R fun (xy : X×Y) => xy.1 := by fun_prop

-- #generate_linear_map_simps Prod.fst.arg_self.IsLinearMap_rule_simple


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.snd.arg_self.IsLinearMap_rule
    (f : X → Y×Z) (hf : IsLinearMap R f) : IsLinearMap R fun (x : X) => (f x).snd :=
  by_linear_map ((LinearMap.snd _ _ _).comp (mk' _ hf)) (by simp)


theorem Prod.snd.arg_self.IsLinearMap_rule_simple :
    IsLinearMap R fun (xy : X×Y) => xy.2 := by fun_prop

-- #generate_linear_map_simps Prod.snd.arg_self.IsLinearMap_rule_simple

--------------------------------------------------------------------------------


theorem Prod.mk.arg_fstsnd.IsLinearMap_rule_simple
  : IsLinearMap R fun xy : X×Y => (xy.1, xy.2) := by fun_prop

-- #generate_linear_map_simps Prod.mk.arg_fstsnd.IsLinearMap_rule_simple


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
  by_linear_map (a.comp b) (by simp (config:={zetaDelta:=true}))

@[fun_prop]
theorem HSMul.hSMul.arg_a1.IsLinearMap_rule_nat
    (c : ℕ) (f : X → Y) (hf : IsLinearMap R f) : IsLinearMap R fun x => c • f x := by
  constructor
  intro x y; simp[hf.1]
  intro c x; simp[hf.2]; rw [@smul_algebra_smul_comm]


@[fun_prop]
theorem HSMul.hSMul.arg_a1.IsLinearMap_rule_int
    (c : ℤ) (f : X → Y) (hf : IsLinearMap R f) : IsLinearMap R fun x => c • f x := by
  constructor
  intro x y; simp[hf.1]
  intro c x; simp[hf.2]; rw [@smul_comm]

-- sum ----------------------------------------------------------------
--------------------------------------------------------------------------------

-- @[fun_prop]
-- theorem sum.arg_f.IsLinearMap_rule
--   (f : X → ι → Y) (hf : ∀ i, IsLinearMap R (f · i))
--   : IsLinearMap R fun x => ∑ i, f x i := by sorry_proof


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
  by_linear_map (a.comp b) (by simp (config:={zetaDelta:=true}))


@[fun_prop]
theorem HMul.hMul.arg_a0.IsLinearMap_rule
    (f : X → R) (hf : IsLinearMap R f) (y' : R) : IsLinearMap R fun x => f x * y' := by
  constructor
  intro x y; rw[hf.1]; exact RightDistribClass.right_distrib (f x) (f y) y'
  intro c x; rw[hf.2]; exact smul_mul_assoc c (f x) y'


@[fun_prop]
theorem HMul.hMul.arg_a1.IsLinearMap_rule
  (f : X → R) (hf : IsLinearMap R f) (y' : R) : IsLinearMap R fun x => y' * f x := by
  constructor
  intro x y; rw[hf.1]; exact LeftDistribClass.left_distrib y' (f x) (f y)
  intro c x; rw[hf.2]; exact mul_smul_comm c y' (f x)


end CommSemiring



section OnAdjointSpace
open SciLean
variable
  {R : Type _} [RealScalar R]
  {X : Type _} [NormedAddCommGroup X] [AdjointSpace R X]

theorem Inner.inner.arg_a0.IsLinearMap_rule' (y : X) :
    IsLinearMap R (fun x : X => ⟪x,y⟫[R]) := sorry_proof

#generate_linear_map_simps Inner.inner.arg_a0.IsLinearMap_rule'

theorem Inner.inner.arg_a1.IsLinearMap_rule' (y : X) :
    IsLinearMap R (fun x : X => ⟪y,x⟫[R]) := sorry_proof

#generate_linear_map_simps Inner.inner.arg_a1.IsLinearMap_rule'


end OnAdjointSpace


-- namespace SciLean

-- section OnFinVec

-- variable
--   {K : Type _} [RCLike K]
--   {IX : Type _} [IndexType IX] [DecidableEq IX] {X : Type _} [FinVec IX K X]
--   {IY : Type _} [IndexType IY] [DecidableEq IY] {Y : Type _} [FinVec IY K Y]
--   {IZ : Type _} [IndexType IZ] [DecidableEq IZ] {Z : Type _} [FinVec IZ K Z]

-- @[fun_prop]
-- theorem Basis.proj.arg_x.IsLinearMap_rule (i : IX) :
--     IsLinearMap K (fun x : X => ℼ i x) := by sorry_proof

-- #generate_linear_map_simps SciLean.Basis.proj.arg_x.IsLinearMap_rule

-- @[fun_prop]
-- theorem DualBasis.dualProj.arg_x.IsLinearMap_rule (i : IX) :
--     IsLinearMap K (fun x : X => ℼ' i x) := by sorry_proof

-- #generate_linear_map_simps SciLean.DualBasis.dualProj.arg_x.IsLinearMap_rule

-- @[fun_prop]
-- theorem BasisDuality.toDual.arg_x.IsLinearMap_rule :
--     IsLinearMap K (fun x : X => BasisDuality.toDual x) := by sorry_proof

-- #generate_linear_map_simps SciLean.BasisDuality.toDual.arg_x.IsLinearMap_rule

-- @[fun_prop]
-- theorem BasisDuality.fromDual.arg_x.IsLinearMap_rule :
--     IsLinearMap K (fun x : X => BasisDuality.fromDual x) := by sorry_proof

-- #generate_linear_map_simps SciLean.BasisDuality.fromDual.arg_x.IsLinearMap_rule

-- end OnFinVec
-- end SciLean
