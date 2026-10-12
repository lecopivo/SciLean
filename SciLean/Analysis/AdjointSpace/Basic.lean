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

/-- The inner product of an `AdjointSpace` satisfies the axioms of a semi-inner product, i.e. it
gives rise to `PreInnerProductSpace.Core`. This is used to obtain the Cauchy-Schwarz inequality. -/
noncomputable def toPreInnerProductSpaceCore : PreInnerProductSpace.Core 𝕜 E where
  inner x y := ⟪x, y⟫
  conj_inner_symm := conj_symm
  re_inner_nonneg := by
    intro x
    obtain ⟨c,_,hc,_,h⟩ := inner_top_equiv_norm (𝕜:=𝕜) (E:=E)
    have h' : (0:ℝ) ≤ c • ‖x‖^2 := by positivity
    exact le_trans h' (h x).1
  add_left := add_left
  smul_left := smul_left

/-- Cauchy-Schwarz inequality. -/
theorem inner_mul_inner_self_le (x y : E) :
    ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ := by
  letI : PreInnerProductSpace.Core 𝕜 E := toPreInnerProductSpaceCore 𝕜
  exact InnerProductSpace.Core.inner_mul_inner_self_le (𝕜:=𝕜) x y

/-- The inner product is bounded by the norm up to a constant. Unlike for inner product spaces,
the constant can't be taken to be one as the norm does not have to come from the inner product. -/
theorem exists_norm_inner_le : ∃ C : ℝ, 0 < C ∧ ∀ x y : E, ‖⟪x, y⟫‖ ≤ C * (‖x‖ * ‖y‖) := by
  obtain ⟨c,d,hc,hd,h⟩ := inner_top_equiv_norm (𝕜:=𝕜) (E:=E)
  refine ⟨d, hd, fun x y => ?_⟩
  have h1 := inner_mul_inner_self_le 𝕜 x y
  rw [norm_inner_symm y x] at h1
  have h2 : re ⟪x, x⟫ ≤ d * ‖x‖^2 := by simpa using (h x).2
  have h3 : re ⟪y, y⟫ ≤ d * ‖y‖^2 := by simpa using (h y).2
  have h0y : (0:ℝ) ≤ re ⟪y, y⟫ := by
    have : (0:ℝ) ≤ c • ‖y‖^2 := by positivity
    linarith [(h y).1]
  have key : ‖⟪x, y⟫‖ * ‖⟪x, y⟫‖ ≤ (d * (‖x‖*‖y‖)) * (d * (‖x‖*‖y‖)) := by
    refine le_trans h1 ?_
    nlinarith [mul_le_mul h2 h3 h0y (by positivity : (0:ℝ) ≤ d * ‖x‖^2)]
  by_contra hcon
  rw [not_le] at hcon
  exact absurd key (not_le.mpr (mul_self_lt_mul_self (by positivity) hcon))




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
    have ⟨cx,dx,hcx,hdx,hx⟩ := inner_top_equiv_norm (𝕜:=𝕜) (E:=X)
    have ⟨cy,dy,hcy,hdy,hy⟩ := inner_top_equiv_norm (𝕜:=𝕜) (E:=Y)
    refine ⟨min cx cy, dx + dy, lt_min hcx hcy, by positivity, ?_⟩
    intro (x,y)
    obtain ⟨hx1, hx2⟩ := hx x
    obtain ⟨hy1, hy2⟩ := hy y
    have hn : ‖(x,y)‖ = max ‖x‖ ‖y‖ := Prod.norm_def _
    have hxn : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
    have hyn : (0:ℝ) ≤ ‖y‖ := norm_nonneg y
    show min cx cy • ‖(x,y)‖^2 ≤ re (⟪x,x⟫_𝕜 + ⟪y,y⟫_𝕜)
         ∧ re (⟪x,x⟫_𝕜 + ⟪y,y⟫_𝕜) ≤ (dx+dy) • ‖(x,y)‖^2
    rw [hn, map_add]
    simp only [smul_eq_mul] at hx1 hx2 hy1 hy2 ⊢
    rcases le_total ‖x‖ ‖y‖ with h | h
    · have hsq : ‖x‖^2 ≤ ‖y‖^2 := by nlinarith
      rw [max_eq_right h]
      exact ⟨by nlinarith [min_le_left cx cy, min_le_right cx cy], by nlinarith⟩
    · have hsq : ‖y‖^2 ≤ ‖x‖^2 := by nlinarith
      rw [max_eq_left h]
      exact ⟨by nlinarith [min_le_left cx cy, min_le_right cx cy], by nlinarith⟩
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
    choose cf df hcf hdf hbound using
      fun i => AdjointSpace.inner_top_equiv_norm (𝕜:=𝕜) (E:=E i)
    by_cases hι : (Finset.univ : Finset ι).Nonempty
    · refine ⟨Finset.univ.inf' hι cf, ∑ i, df i, ?_, ?_, ?_⟩
      · exact (Finset.lt_inf'_iff hι).2 fun i _ => hcf i
      · exact Finset.sum_pos (fun i _ => hdf i) hι
      · intro x
        have hsum : re (inner 𝕜 x x) = ∑ i, re (inner 𝕜 (x i) (x i)) := by
          show re (∑ᴵ i, ⟪ x i, x i ⟫_𝕜) = _
          rw [SciLean.IndexType.sum_eq_finset_sum, map_sum]
        obtain ⟨i₀, hi₀⟩ := Finset.exists_mem_eq_sup' hι (fun i => ‖x i‖₊)
        have hnorm : ‖x‖ = ‖x i₀‖ := by
          rw [Pi.norm_def, ← Finset.sup'_eq_sup hι, hi₀.2]; rfl
        have hnonneg : ∀ i, 0 ≤ re (inner 𝕜 (x i) (x i)) := fun i =>
          le_trans (by rw [smul_eq_mul]; exact mul_nonneg (hcf i).le (sq_nonneg _))
            (hbound i (x i)).1
        constructor
        · rw [hsum]
          calc Finset.univ.inf' hι cf • ‖x‖^2
              ≤ cf i₀ • ‖x i₀‖^2 := by
                rw [hnorm, smul_eq_mul, smul_eq_mul]
                exact mul_le_mul_of_nonneg_right (Finset.inf'_le _ (Finset.mem_univ i₀))
                  (by positivity)
            _ ≤ re (inner 𝕜 (x i₀) (x i₀)) := (hbound i₀ (x i₀)).1
            _ ≤ ∑ i, re (inner 𝕜 (x i) (x i)) :=
                Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ i₀)
        · rw [hsum, Finset.sum_smul]
          refine Finset.sum_le_sum fun i _ => le_trans (hbound i (x i)).2 ?_
          rw [smul_eq_mul, smul_eq_mul]
          exact mul_le_mul_of_nonneg_left
            (by gcongr; exact norm_le_pi_norm x i) (hdf i).le
    · have hempty : IsEmpty ι := by
        rw [Finset.not_nonempty_iff_eq_empty, Finset.univ_eq_empty_iff] at hι
        exact hι
      refine ⟨1, 1, one_pos, one_pos, fun x => ?_⟩
      have hx : x = 0 := funext fun i => hempty.elim i
      have h0 : re (inner 𝕜 x x) = 0 := by
        show re (∑ᴵ i, ⟪ x i, x i ⟫_𝕜) = 0
        rw [SciLean.IndexType.sum_eq_finset_sum, Finset.univ_eq_empty, Finset.sum_empty, map_zero]
      subst hx
      simp [h0]
  conj_symm := by
    intro x y
    show conj (∑ᴵ i, ⟪y i, x i⟫_𝕜) = ∑ᴵ i, ⟪x i, y i⟫_𝕜
    rw [SciLean.IndexType.sum_eq_finset_sum, SciLean.IndexType.sum_eq_finset_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => AdjointSpace.conj_symm _ _
  add_left := by
    intro x y z
    show (∑ᴵ i, ⟪x i + y i, z i⟫_𝕜) = (∑ᴵ i, ⟪x i, z i⟫_𝕜) + (∑ᴵ i, ⟪y i, z i⟫_𝕜)
    rw [SciLean.IndexType.sum_eq_finset_sum, SciLean.IndexType.sum_eq_finset_sum, SciLean.IndexType.sum_eq_finset_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => AdjointSpace.add_left _ _ _
  smul_left := by
    intro x y r
    show (∑ᴵ i, ⟪r • x i, y i⟫_𝕜) = conj r * ∑ᴵ i, ⟪x i, y i⟫_𝕜
    rw [SciLean.IndexType.sum_eq_finset_sum, SciLean.IndexType.sum_eq_finset_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => AdjointSpace.smul_left _ _ _

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
