module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic

public import SciLean.Util.SorryProof
public import SciLean.Meta.SimpAttr

public import SciLean.Data.IndexType.Basic
public import SciLean.Data.IndexType.Fold
public import SciLean.Data.IndexType.Operations

@[expose] public section


open ComplexConjugate RCLike
/--
This is almost `InnerProductSpace` but we do not require that norm originates from the inner product.

The reason for this class it to be able to have inner product on spaces line `ℝ×ℝ` and `ι → ℝ`
as they are by default equiped by max norm which is not compatible with inner product. -/
class AdjointSpace (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] extends
  NormedSpace 𝕜 E, Inner 𝕜 E where
  /-- Norm induced by inner is topologicaly equivalent to the given norm -/
  inner_top_equiv_norm : ∃ c d : ℝ,
    c > 0 ∧ d > 0 ∧
    ∀ x : E, (c • ‖x‖^2 ≤ re (inner x x)) ∧ (re (inner x x) ≤ d • ‖x‖^2)
  /-- The inner product is *hermitian*, taking the `conj` swaps the arguments. -/
  conj_symm : ∀ x y, conj (inner y x) = inner x y
  /-- The inner product is additive in the first coordinate. -/
  add_left : ∀ x y z, inner (x + y) z = inner x z + inner y z
  /-- The inner product is conjugate linear in the first coordinate. -/
  smul_left : ∀ x y r, inner (r • x) y = conj r * inner x y

attribute [instance low] AdjointSpace.toNormedSpace AdjointSpace.toInner

/-! ### Properties of inner product spaces -/

namespace AdjointSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]

variable [NormedAddCommGroup E] [AdjointSpace 𝕜 E]
variable [NormedAddCommGroup F] [AdjointSpace ℝ F]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y
local notation "‖" x "‖₂²" => @inner 𝕜 E _ x x

local notation "IK" => @RCLike.I 𝕜 _

local postfix:90 "†" => starRingEnd _

export InnerProductSpace (norm_sq_eq_re_inner)

open RCLike ComplexConjugate InnerProductSpace

section BasicProperties

@[simp mid+1, simp_core mid+1]
theorem inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫ := by rw[conj_symm]

theorem real_inner_comm (x y : F) : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by
  rw[← conj_symm]; simp only [conj_trivial]

theorem inner_eq_zero_symm {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ = 0 := by
  rw [← inner_conj_symm]
  exact star_eq_zero

@[simp mid+1, simp_core mid+1]
theorem inner_self_im (x : E) : RCLike.im ⟪x, x⟫ = 0 := by
  rw [← @ofReal_inj 𝕜, im_eq_conj_sub]; simp

theorem inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ := by rw[add_left]

theorem inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ := by
  rw [← inner_conj_symm, inner_add_left, RingHom.map_add]
  simp only [inner_conj_symm]

theorem inner_re_symm (x y : E) : re ⟪x, y⟫ = re ⟪y, x⟫ := by rw [← inner_conj_symm, conj_re]

theorem inner_im_symm (x y : E) : im ⟪x, y⟫ = -im ⟪y, x⟫ := by rw [← inner_conj_symm, conj_im]

theorem inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪x, y⟫ := by rw [smul_left]

theorem real_inner_smul_left (x y : F) (r : ℝ) : ⟪r • x, y⟫_ℝ = r * ⟪x, y⟫_ℝ :=
  inner_smul_left _ _ _

theorem inner_smul_real_left (x y : E) (r : ℝ) : ⟪(r : 𝕜) • x, y⟫ = r • ⟪x, y⟫ := by
  rw [inner_smul_left, conj_ofReal, Algebra.smul_def]

theorem inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * ⟪x, y⟫ := by
  rw [← inner_conj_symm, inner_smul_left, RingHom.map_mul, conj_conj, inner_conj_symm]

theorem real_inner_smul_right (x y : F) (r : ℝ) : ⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ :=
  inner_smul_right _ _ _

theorem inner_smul_real_right (x y : E) (r : ℝ) : ⟪x, (r : 𝕜) • y⟫ = r • ⟪x, y⟫ := by
  rw [inner_smul_right, Algebra.smul_def]

/-- The inner product as a sesquilinear form.

Note that in the case `𝕜 = ℝ` this is a bilinear form. -/
@[simps!]
def sesqFormOfInner : E →ₗ[𝕜] E →ₗ⋆[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ (RingHom.id 𝕜) (starRingEnd _) (fun x y => ⟪y, x⟫)
    (fun _x _y _z => inner_add_right _ _ _) (fun _r _x _y => inner_smul_right _ _ _)
    (fun _x _y _z => inner_add_left _ _ _) fun _r _x _y => inner_smul_left _ _ _


/-- An inner product with a sum on the left. -/
theorem sum_inner {ι : Type*} (s : Finset ι) (f : ι → E) (x : E) :
    ⟪∑ i ∈ s, f i, x⟫ = ∑ i ∈ s, ⟪f i, x⟫ :=
  map_sum (sesqFormOfInner (𝕜 := 𝕜) (E := E) x) _ _

/-- An inner product with a sum on the right. -/
theorem inner_sum {ι : Type*} (s : Finset ι) (f : ι → E) (x : E) :
    ⟪x, ∑ i ∈ s, f i⟫ = ∑ i ∈ s, ⟪x, f i⟫ :=
  map_sum (LinearMap.flip sesqFormOfInner x) _ _

@[simp mid+1, simp_core mid+1]
theorem inner_zero_left (x : E) : ⟪0, x⟫ = 0 := by
  rw [← zero_smul 𝕜 (0 : E), inner_smul_left, RingHom.map_zero, zero_mul]

theorem inner_re_zero_left (x : E) : re ⟪0, x⟫ = 0 := by
  simp only [inner_zero_left, AddMonoidHom.map_zero]

@[simp mid+1, simp_core mid+1]
theorem inner_zero_right (x : E) : ⟪x, 0⟫ = 0 := by
  rw [← inner_conj_symm, inner_zero_left, RingHom.map_zero]

theorem inner_re_zero_right (x : E) : re ⟪x, 0⟫ = 0 := by
  simp only [inner_zero_right, AddMonoidHom.map_zero]

theorem inner_self_nonneg {x : E} : 0 ≤ re ⟪x, x⟫ := by
  have ⟨c,d,hc,_,h⟩ := inner_top_equiv_norm (𝕜:=𝕜) (E:=E)
  have ⟨h'',_⟩ := h x
  apply le_trans _ h''
  positivity

theorem real_inner_self_nonneg {x : F} : 0 ≤ ⟪x, x⟫_ℝ :=
  @inner_self_nonneg ℝ F _ _ _ x

@[simp mid+1, simp_core mid+1]
theorem inner_self_ofReal_re (x : E) : (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ :=
  ((RCLike.is_real_TFAE (⟪x, x⟫ : 𝕜)).out 3 4).2 (inner_self_im _)

@[simp mid+1, simp_core mid+1]
theorem inner_self_nonpos {x : E} : re ⟪x, x⟫ ≤ 0 ↔ x = 0 := by
  constructor
  · have ⟨c,d,hc,_,h⟩ := inner_top_equiv_norm (𝕜:=𝕜) (E:=E)
    have ⟨h,_⟩ := h x
    intro h'; simp[] at h
    have : ‖x‖^2 ≤ 0 := by nlinarith
    have : ‖x‖ ≤ 0 := by nlinarith
    simp_all only [gt_iff_lt, smul_eq_mul, norm_le_zero_iff]
  · simp_all only [inner_zero_right, map_zero, le_refl, implies_true]

theorem real_inner_self_nonpos {x : F} : ⟪x, x⟫_ℝ ≤ 0 ↔ x = 0 :=
  @inner_self_nonpos ℝ F _ _ _ x

@[simp mid+1, simp_core mid+1]
theorem inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply (inner_self_nonpos (𝕜:=𝕜)).1
    simp only [h, map_zero, le_refl]
  · simp_all only [inner_zero_right, implies_true]

theorem inner_self_ne_zero {x : E} : ⟪x, x⟫ ≠ 0 ↔ x ≠ 0 :=
  inner_self_eq_zero.not

theorem norm_inner_symm (x y : E) : ‖⟪x, y⟫‖ = ‖⟪y, x⟫‖ := by rw [← inner_conj_symm, norm_conj]


@[simp mid+1, simp_core mid+1]
theorem inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫ := by
  rw [← neg_one_smul 𝕜 x, inner_smul_left]
  simp

@[simp mid+1, simp_core mid+1]
theorem inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫ := by
  rw [← inner_conj_symm, inner_neg_left]; simp only [RingHom.map_neg, inner_conj_symm]

theorem inner_neg_neg (x y : E) : ⟪-x, -y⟫ = ⟪x, y⟫ := by simp

-- Porting note: removed `simp` because it can prove it using `inner_conj_symm`
theorem inner_self_conj (x : E) : ⟪x, x⟫† = ⟪x, x⟫ := inner_conj_symm _ _

theorem inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by
  simp [sub_eq_add_neg, inner_add_left]

theorem inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by
  simp [sub_eq_add_neg, inner_add_right]

theorem inner_mul_symm_re_eq_norm (x y : E) : re (⟪x, y⟫ * ⟪y, x⟫) = ‖⟪x, y⟫ * ⟪y, x⟫‖ := by
  rw [← inner_conj_symm, mul_comm]
  exact re_eq_norm_of_mul_conj (inner 𝕜 y x)

/-- Expand `⟪x + y, x + y⟫` -/
theorem inner_add_add_self (x y : E) : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_add_left, inner_add_right]; ring

/-- Expand `⟪x + y, x + y⟫_ℝ` -/
theorem real_inner_add_add_self (x y : F) :
    ⟪x + y, x + y⟫_ℝ = ⟪x, x⟫_ℝ + 2 * ⟪x, y⟫_ℝ + ⟪y, y⟫_ℝ := by
  have : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by rw [← inner_conj_symm]; rfl
  simp only [inner_add_add_self, this, add_left_inj]
  ring

-- Expand `⟪x - y, x - y⟫`
theorem inner_sub_sub_self (x y : E) : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_sub_left, inner_sub_right]; ring

/-- Expand `⟪x - y, x - y⟫_ℝ` -/
theorem real_inner_sub_sub_self (x y : F) :
    ⟪x - y, x - y⟫_ℝ = ⟪x, x⟫_ℝ - 2 * ⟪x, y⟫_ℝ + ⟪y, y⟫_ℝ := by
  have : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by rw [← inner_conj_symm]; rfl
  simp only [inner_sub_sub_self, this, add_left_inj]
  ring

variable (𝕜)

theorem ext_inner_left {x y : E} (h : ∀ v, ⟪v, x⟫ = ⟪v, y⟫) : x = y := by
  rw [← sub_eq_zero, ← @inner_self_eq_zero 𝕜, inner_sub_right, sub_eq_zero, h (x - y)]

theorem ext_inner_right {x y : E} (h : ∀ v, ⟪x, v⟫ = ⟪y, v⟫) : x = y := by
  rw [← sub_eq_zero, ← @inner_self_eq_zero 𝕜, inner_sub_left, sub_eq_zero, h (x - y)]




/-- The inner product as a sesquilinear map. -/
def innerₛₗ : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ _ _ (fun v w => ⟪v, w⟫) inner_add_left (fun _ _ _ => inner_smul_left _ _ _)
    inner_add_right fun _ _ _ => inner_smul_right _ _ _

@[simp mid+1, simp_core mid+1]
theorem innerₛₗ_apply_coe (v : E) : ⇑(innerₛₗ 𝕜 v) = fun w => ⟪v, w⟫ :=
  rfl

@[simp]
theorem innerₛₗ_apply (v w : E) : innerₛₗ 𝕜 v w = ⟪v, w⟫ :=
  rfl

variable (F)
/-- The inner product as a bilinear map in the real case. -/
noncomputable
def innerₗ : F →ₗ[ℝ] F →ₗ[ℝ] ℝ := innerₛₗ ℝ

@[simp] lemma flip_innerₗ : (innerₗ F).flip = innerₗ F := by
  ext v w
  exact real_inner_comm v w



----------------------------------------------------------------------------------------------------
-- Instances ---------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
variable
  {X} [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
  {Y} [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]

instance : AdjointSpace 𝕜 𝕜 where
  inner_top_equiv_norm := by
    apply Exists.intro 1
    apply Exists.intro 1
    simp [norm_sq_eq_def]
  conj_symm := by simp[mul_comm]
  add_left := by simp[mul_add]
  smul_left := by simp; intros; ac_rfl

instance : Inner 𝕜 Unit where
  inner _ _ := 0

instance : AdjointSpace 𝕜 Unit where
  inner_top_equiv_norm := by
    apply Exists.intro 1
    apply Exists.intro 1
    simp[Inner.inner]
  conj_symm := by simp[Inner.inner]
  add_left := by simp[Inner.inner]
  smul_left := by simp[Inner.inner]

instance : AdjointSpace 𝕜 (X×Y) where
  inner := fun (x,y) (x',y') => ⟪x,x'⟫_𝕜 + ⟪y,y'⟫_𝕜
  inner_top_equiv_norm := by
    have ⟨cx,dx,hcx,hdx,_hx⟩ := inner_top_equiv_norm (𝕜:=𝕜) (E:=X)
    have ⟨cy,dy,hcy,hdy,_hy⟩ := inner_top_equiv_norm (𝕜:=𝕜) (E:=X)
    apply Exists.intro (cx*cx + cy*cy) -- todo: fix this constant
    apply Exists.intro (dx*dx + dy*dy) -- todo: fix this constant
    constructor
    · positivity
    constructor
    · positivity
    · intro (x,y)
      sorry_proof
  conj_symm := by simp
  add_left := by simp[inner_add_left]; intros; ac_rfl
  smul_left := by simp[inner_smul_left,mul_add]


variable
  {ι : Type*} {n} [SciLean.IndexType ι n] [SciLean.Fold ι]
  {E : ι → Type*}

instance {𝕜 : Type*} [AddCommMonoid 𝕜] [∀ i, Inner 𝕜 (E i)] :
    Inner 𝕜 ((i : ι) → E i) where
  inner := fun x y => ∑ᴵ i, ⟪x i, y i⟫_𝕜

open Classical in
instance [∀ i, NormedAddCommGroup (E i)] [∀ i, AdjointSpace 𝕜 (E i)] :
    AdjointSpace 𝕜 ((i : ι) → E i) where
  inner_top_equiv_norm := by
    -- have h := fun i => inner_top_equiv_norm (𝕜:=𝕜) (E:=E i)
    -- let c := (fun i => let ci := choose (h i); ci*ci)
    -- let d := (fun i => let di := choose <| choose_spec (h i); di*di)
    -- universe issues with IndexType :(
    -- apply Exists.intro (∑ i, c i ^ 2)
    -- apply Exists.intro (∑ i, d i ^ 2)
    sorry_proof
  conj_symm := by simp[Inner.inner]; sorry_proof
  add_left := by simp[Inner.inner, inner_add_left]; sorry_proof
  smul_left := by simp[Inner.inner, inner_smul_left]; sorry_proof

-- deprecate these
theorem inner_prod_split (x y : X×Y) : ⟪x,y⟫_𝕜 = ⟪x.1,y.1⟫_𝕜 + ⟪x.2,y.2⟫_𝕜 := by rfl
theorem inner_forall_split [∀ i, NormedAddCommGroup (E i)] [∀ i, AdjointSpace 𝕜 (E i)]
    (f g : (i : ι) → E i) :
    ⟪f,g⟫_𝕜 = ∑ᴵ i, ⟪f i, g i⟫_𝕜 := by rfl

-- prefere these
-- theorem inner_prod_def (x y : X×Y) : ⟪x,y⟫_𝕜 = ⟪x.1,y.1⟫_𝕜 + ⟪x.2,y.2⟫_𝕜 := by rfl
-- theorem inner_forall_def [∀ i, NormedAddCommGroup (E i)] [∀ i, AdjointSpace 𝕜 (E i)]
--     (f g : (i : ι) → E i) :
--     ⟪f,g⟫_𝕜 = ∑ᴵ i, ⟪f i, g i⟫_𝕜 := by rfl
