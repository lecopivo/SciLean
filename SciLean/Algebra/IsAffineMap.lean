module

public import Mathlib.Algebra.Module.LinearMap.Basic
public import SciLean.Algebra.IsLinearMap

@[expose] public section


set_option linter.unusedVariables false

open SciLean

--------------------------------------------------------------------------------

set_option deprecated.oldSectionVars true

variable {R X Y Z ι : Type _} {E : ι → Type _}
  [CommRing R]
  [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y]
  [AddCommGroup Z] [Module R Z]
  -- [IndexType ι] [DecidableEq ι]
  [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]

variable (R)
-- poor man's version of affine map
-- todo: align with mathlib more in particular it should be defined ove affine space rather then
--       over module
--       see: https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/AffineSpace.20class

@[fun_prop]
structure IsAffineMap (f : X → Y) : Prop where
  is_affine : IsLinearMap R (fun x => f x - f 0)

variable {R}

namespace IsAffineMap

attribute [fun_prop] IsAffineMap

theorem map_add' {f : X → Y} (hf : IsAffineMap R f) (x y : X) :
    f (x + y) = f x + f y - f 0 := by
  rw [sub_eq_iff_eq_add.mp (hf.is_affine.map_add x y)]; abel

theorem map_smul' {f : X → Y} (hf : IsAffineMap R f) (c : R) (x : X) :
    f (c • x) = c • f x + (1 - c) • f 0 := by
  rw [sub_eq_iff_eq_add.mp (hf.is_affine.map_smul c x)]
  module

/-- Affine maps are exactly the maps satisfying these two identities. -/
theorem mk' {f : X → Y}
    (hadd : ∀ x y, f (x + y) = f x + f y - f 0)
    (hsmul : ∀ (c : R) x, f (c • x) = c • f x + (1 - c) • f 0) : IsAffineMap R f := by
  constructor
  constructor
  · intro x y; simp only [hadd]; abel
  · intro c x; simp only [hsmul]; module

@[fun_prop]
theorem id_rule : IsAffineMap R (fun x : X ↦ x) := by constructor; simp; fun_prop

@[fun_prop]
theorem const_rule (y : Y)
  : IsAffineMap R (fun _ : X => y)
  := by constructor; simp; apply IsLinearMap.const_zero_rule

@[fun_prop]
theorem comp_rule {f : Y → Z} {g : X → Y}
    (hf : IsAffineMap R f) (hg : IsAffineMap R g) : IsAffineMap R (fun x ↦ f (g x)) := by
  apply mk' (R:=R)
  · intro x y
    simp only [hg.map_add', sub_eq_add_neg, ← neg_one_smul R (g 0), hf.map_add', hf.map_smul']
    module
  · intro c x
    simp only [hg.map_smul', hf.map_add', hf.map_smul']
    module

@[fun_prop]
theorem apply_rule (i : ι) : IsAffineMap R (fun f : (i : ι) → E i ↦ f i) := by
  constructor
  constructor
  simp
  simp

@[fun_prop]
theorem IsAffineMap_pi (f : X → (i : ι) → E i) (hf : ∀ i, IsAffineMap R (f · i)) :
    IsAffineMap R (fun x i ↦ f x i) := by
  apply mk' (R:=R) <;> intros <;> funext i <;> simp [(hf i).map_add', (hf i).map_smul']


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

@[fun_prop]
theorem ofLinear (f : X → Y) (hf : IsLinearMap R f) : IsAffineMap R f := by
  constructor
  simp[hf.map_zero,hf]

/-- Restriction of scalars: an `R`-affine map is `S`-affine as soon as `S` acts on `X` and `Y`
through `R`. -/
theorem restrictScalars {S : Type*} [CommRing S] [Module S R] [Module S X] [Module S Y]
    [IsScalarTower S R X] [IsScalarTower S R Y]
    {f : X → Y} (hf : IsAffineMap R f) : IsAffineMap S f := by
  apply mk' (R:=S)
  · exact hf.map_add'
  · intro s x
    rw [show s • x = (s • (1:R)) • x from (smul_one_smul R s x).symm, hf.map_smul',
      smul_one_smul, ← smul_one_smul R ((1:S) - s) (f 0), sub_smul, one_smul]
    simp [sub_smul]


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
  : IsAffineMap R fun x => (g x, f x) := by
  apply mk' (R:=R) <;> intros <;>
    simp [hf.map_add', hg.map_add', hf.map_smul', hg.map_smul']


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.fst.arg_self.IsAffineMap_rule
    (f : X → Y×Z) (hf : IsAffineMap R f) : IsAffineMap R fun (x : X) => (f x).fst := by
  apply mk' (R:=R)
  · intro x y; rw [hf.map_add']; rfl
  · intro c x; rw [hf.map_smul']; rfl


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.snd.arg_self.IsAffineMap_rule
    (f : X → Y×Z) (hf : IsAffineMap R f) : IsAffineMap R fun (x : X) => (f x).snd := by
  apply mk' (R:=R)
  · intro x y; rw [hf.map_add']; rfl
  · intro c x; rw [hf.map_smul']; rfl


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Neg.neg.arg_a0.IsAffineMap_rule
    (f : X → Y) (hf : IsAffineMap R f) : IsAffineMap R fun x => - f x := by
  apply mk' (R:=R) <;> intros <;> simp only [hf.map_add', hf.map_smul'] <;> module


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HAdd.hAdd.arg_a0a1.IsAffineMap_rule
    (f g : X → Y) (hf : IsAffineMap R f) (hg : IsAffineMap R g) :
    IsAffineMap R fun x => f x + g x := by
  apply mk' (R:=R) <;> intros <;>
    simp only [hf.map_add', hg.map_add', hf.map_smul', hg.map_smul'] <;> module



-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HSub.hSub.arg_a0a1.IsAffineMap_rule
    (f g : X → Y) (hf : IsAffineMap R f) (hg : IsAffineMap R g) :
    IsAffineMap R fun x => f x - g x := by
  apply mk' (R:=R) <;> intros <;>
    simp only [hf.map_add', hg.map_add', hf.map_smul', hg.map_smul'] <;> module

-- Smul.smul ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HSMul.hSMul.arg_a0.IsAffineMap_rule
    (f : X → R) (y : Y) (hf : IsAffineMap R f) : IsAffineMap R fun x => f x • y := by
  apply mk' (R:=R)
  · intros; simp only [hf.map_add', add_smul, sub_smul]
  · intros; simp only [hf.map_smul', add_smul]; module

@[fun_prop]
theorem HSMul.hSMul.arg_a1.IsAffineMap_rule
    (c : R) (f : X → Y) (hf : IsAffineMap R f) : IsAffineMap R fun x => c • f x := by
  apply mk' (R:=R) <;> intros <;> simp only [hf.map_add', hf.map_smul'] <;> module

/-- Note: compared to the original statement this rule assumes that `S` acts on `R` and that both
actions on `X` and `Y` factor through `R` (`IsScalarTower S R X` and `IsScalarTower S R Y`).
Without such compatibility an `R`-affine map need not be `S`-affine at all. -/
@[fun_prop]
theorem HSMul.hSMul.arg_a1.IsAffineMap_rule' {S} [CommRing S] [Module S R] [Module S X] [Module S Y]
    [IsScalarTower S R X] [IsScalarTower S R Y]
    (c : R) (f : X → Y) (hf : IsAffineMap R f) : IsAffineMap S fun x => c • f x := by
  have hlin : IsLinearMap S (fun y : Y => c • y) := by
    constructor
    · intro y y'; exact smul_add c y y'
    · intro s y
      rw [← smul_one_smul R s y, ← smul_one_smul R s (c • y), smul_smul, smul_smul, mul_comm]
  exact comp_rule (ofLinear _ hlin) (hf.restrictScalars (S:=S))


@[fun_prop]
theorem HSMul.hSMul.arg_a1.IsAffineMap_rule_nat
    (c : ℕ) (f : X → Y) (hf : IsAffineMap R f) : IsAffineMap R fun x => c • f x := by
  apply mk' (R:=R) <;> intros <;>
    simp only [hf.map_add', hf.map_smul', smul_add, smul_sub, smul_comm c]

@[fun_prop]
theorem HSMul.hSMul.arg_a1.IsAffineMap_rule_int
    (c : ℤ) (f : X → Y) (hf : IsAffineMap R f) : IsAffineMap R fun x => c • f x := by
  apply mk' (R:=R) <;> intros <;>
    simp only [hf.map_add', hf.map_smul', smul_add, smul_sub, smul_comm c]

-- HMul.hMul ------------------------------------------------------------------
--------------------------------------------------------------------------------

/-- Note: compared to the original statement this rule additionally assumes `IsScalarTower 𝕜 R R`,
i.e. that the `𝕜`-action on `R` is given by multiplication with `(· • 1)`. -/
@[fun_prop]
theorem HMul.hMul.arg_a0.IsAffineMap_rule
  {𝕜 : Type*} [RCLike 𝕜] [Module 𝕜 R] [Module 𝕜 X] [IsScalarTower 𝕜 R X] [IsScalarTower 𝕜 R R]
  (f : X → R) (hf : IsAffineMap R f) (y' : R) : IsAffineMap 𝕜 fun x => f x * y' := by
  have hlin : IsLinearMap 𝕜 (fun r : R => r * y') := by
    constructor
    · intro r r'; exact add_mul r r' y'
    · intro c r; exact smul_mul_assoc c r y'
  exact comp_rule (ofLinear _ hlin) (hf.restrictScalars (S:=𝕜))

@[fun_prop]
theorem HMul.hMul.arg_a1.IsAffineMap_rule
  {𝕜 : Type*} [RCLike 𝕜] [Module 𝕜 R] [Module 𝕜 X] [IsScalarTower 𝕜 R X] [IsScalarTower 𝕜 R R]
  (f : X → R) (hf : IsAffineMap R f) (y' : R) : IsAffineMap 𝕜 fun x => y' * f x := by
  have h : (fun x => y' * f x) = (fun x => f x * y') := by funext x; rw [mul_comm]
  rw [h]
  exact HMul.hMul.arg_a0.IsAffineMap_rule f hf y'


-- sum ----------------------------------------------------------------
--------------------------------------------------------------------------------

-- @[fun_prop]
-- theorem sum.arg_f.IsAffineMap_rule
--   (f : X → ι → Y) (hf : ∀ i, IsAffineMap R (f · i))
--   : IsAffineMap R fun x => ∑ i, f x i := by sorry_proof


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


-- namespace SciLean
-- section OnFinVec

-- variable
--   {K : Type _} [RCLike K]
--   {IX : Type} [IndexType IX] [DecidableEq IX] {X : Type _} [FinVec IX K X]
--   {IY : Type} [IndexType IY] [DecidableEq IY] {Y : Type _} [FinVec IY K Y]
--   {IZ : Type} [IndexType IZ] [DecidableEq IZ] {Z : Type _} [FinVec IZ K Z]

-- @[fun_prop]
-- theorem Basis.proj.arg_x.IsAffineMap_rule (i : IX) :
--     IsAffineMap K (fun x : X => ℼ i x) := by sorry_proof

-- @[fun_prop]
-- theorem DualBasis.dualProj.arg_x.IsAffineMap_rule (i : IX) :
--     IsAffineMap K (fun x : X => ℼ' i x) := by sorry_proof

-- @[fun_prop]
-- theorem BasisDuality.toDual.arg_x.IsAffineMap_rule :
--     IsAffineMap K (fun x : X => BasisDuality.toDual x) := by sorry_proof

-- @[fun_prop]
-- theorem BasisDuality.fromDual.arg_x.IsAffineMap_rule :
--     IsAffineMap K (fun x : X => BasisDuality.fromDual x) := by sorry_proof

-- end OnFinVec
-- end SciLean
