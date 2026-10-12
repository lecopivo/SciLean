module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
-- import Mathlib.MeasureTheory.Integral.Bochner.L1
-- import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory

public import SciLean.Meta.SimpAttr
public import SciLean.Util.SorryProof

@[expose] public section


namespace MeasureTheory

set_option deprecated.oldSectionVars true
variable
  {α} [MeasurableSpace α]
  {E} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [LocallyConvexSpace ℝ E]


def WeakMeasurable (f : α → E) :=
  ∀ e' : E →L[ℝ] ℝ, Measurable (fun x => e' (f x))

def AEWeakMeasurable (f : α → E) (μ : Measure α) :=
  ∃ g : α → E, WeakMeasurable g ∧ f =ᵐ[μ] g

/-- Element `e` is weak(Pettis) integral of `f`

wiki:https://en.wikipedia.org/wiki/Pettis_integral

Also see documentation for `weakIntegral`
-/
def HasWeakIntegral (f : α → E) (e : E) (μ : Measure α) :=
  ∀ (e' : E →L[ℝ] ℝ),
    Integrable (fun x => e' (f x)) μ
    ∧
    ∫ x, e' (f x) ∂μ = e' e


/-- Function `f` is weakly(Pettis) integrable

wiki:https://en.wikipedia.org/wiki/Pettis_integral

Also see documentation for `weakIntegral`
-/
def WeakIntegrable (f : α → E) (μ : Measure α) := ∃ e, HasWeakIntegral f e μ

open Classical in
/-- Weak(Pettis) Integral

Element `e` is weak integral of `f : α → E` if for all elements of the dual space `e' : E →L[ℝ] ℝ`
the integral of `fun x => e' (f x )` is equal to `e' e`, i.e.
```
∀ e', ∫ x, e' (f x) ∂μ = e' e
```

The main reason for introducing weak integral in SciLean is that we can integrate functions like
`f : α → ι → E` where `ι` is arbitrary type, not necessarily finite. Strong(Bochner) integral can
integrate `f : α → ι → E` only if `ι` is finite and `E` is normed space as then `ι → E` is
normed space too.

Our main application is when working with random variables as we can talk about random functions
`f : Rand (ι → E)` for arbitrary `ι` and `E` locally convex vector space.

wiki:https://en.wikipedia.org/wiki/Pettis_integral
 -/
noncomputable
def weakIntegral (μ : Measure α) (f : α → E) : E :=
  if h : WeakIntegrable f μ then
    Classical.choose h
  else
    0

/-- Two weak integrals of the same function agree, provided the continuous linear functionals
separate the points of `E`. -/
theorem HasWeakIntegral.unique [SeparatingDual ℝ E] {f : α → E} {e e' : E} {μ : Measure α}
    (h : HasWeakIntegral f e μ) (h' : HasWeakIntegral f e' μ) : e = e' :=
  (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 (fun g => ((h g).2).symm.trans (h' g).2)

/-- The weak integral is unique.

Compared with the original statement this one assumes `SeparatingDual ℝ E`, i.e. that the
continuous linear functionals separate the points of `E` - without such an assumption `e` is
only determined up to elements that every functional maps to zero. For a locally convex space
this follows from Hahn-Banach as soon as the topology is `T1`, and it holds in particular for
any normed space. -/
theorem weak_integral_unique [SeparatingDual ℝ E] (f : α → E) (e : E) (μ : Measure α) :
    HasWeakIntegral f e μ → e = weakIntegral μ f := by
  intro h
  have hi : WeakIntegrable f μ := ⟨e, h⟩
  have hw : weakIntegral μ f = Classical.choose hi := by
    simp only [weakIntegral, hi, ↓reduceDIte]
  rw [hw]
  exact h.unique (Classical.choose_spec hi)


/-- A Bochner integrable function is weakly(Pettis) integrable, its weak integral being the
Bochner integral.

Compared with the original statement this one assumes `CompleteSpace E`, which is needed for the
Bochner integral to be an element of `E` in the first place. -/
theorem integrable_is_weak_integrable {E} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : α → E) (μ : Measure α) :
    Integrable f μ → WeakIntegrable f μ := by
  intro hf
  exact ⟨∫ x, f x ∂μ, fun e' => ⟨e'.integrable_comp hf, e'.integral_comp_comm hf⟩⟩

/-- For a Bochner integrable function the weak integral is the Bochner integral.

Compared with the original statement this one assumes `CompleteSpace E`, see
`integrable_is_weak_integrable`. -/
theorem weak_integral_eq_integral {E} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : α → E) (μ : Measure α) :
    Integrable f μ → weakIntegral μ f = ∫ x, f x ∂μ := by
  intro hf
  exact (weak_integral_unique f (∫ x, f x ∂μ) μ
    (fun e' => ⟨e'.integrable_comp hf, e'.integral_comp_comm hf⟩)).symm

-- the big advantage of weak integral is
set_option linter.unusedVariables false in
theorem pointwise_integral (f : ι → α → E)
    (hf : ∀ i, WeakIntegrable (f i) μ) :
    weakIntegral μ (fun x => (f · x))
    =
    fun i => weakIntegral μ (fun x => f i x) := sorry_proof

open Classical in
/-- A continuous linear functional on a product depends only on finitely many coordinates. -/
theorem exists_finset_apply_pi_eq_sum {ι : Type*} (φ : ((_ : ι) → E) →L[ℝ] ℝ) :
    ∃ S : Finset ι, ∀ x : ι → E, φ x = ∑ i ∈ S, φ (Pi.single i (x i)) := by
  -- the preimage of `(-1,1)` is a neighbourhood of `0`, hence it contains a basic box
  have h0 : φ ⁻¹' (Set.Ioo (-1:ℝ) 1) ∈ nhds (0 : ι → E) := by
    apply φ.continuous.continuousAt.preimage_mem_nhds
    simpa using Ioo_mem_nhds (by norm_num) (by norm_num)
  rw [nhds_pi, Filter.mem_pi] at h0
  obtain ⟨I, hI, V, hV, hVsub⟩ := h0
  refine ⟨hI.toFinset, fun x => ?_⟩
  -- `φ` vanishes on the vectors that are zero on `I`
  have hzero : ∀ w : ι → E, (∀ i ∈ I, w i = 0) → φ w = 0 := by
    intro w hw
    have hmem : ∀ n : ℕ, (n : ℝ) * |φ w| < 1 := by
      intro n
      have hpi : (n : ℝ) • w ∈ I.pi V := by
        intro i hi
        rw [show ((n : ℝ) • w) i = 0 by simp [hw i hi]]
        exact mem_of_mem_nhds (hV i)
      have h1 := hVsub hpi
      simp only [Set.mem_preimage, map_smul, smul_eq_mul, Set.mem_Ioo] at h1
      have h2 : |(n : ℝ) * φ w| < 1 := abs_lt.2 ⟨h1.1, h1.2⟩
      rwa [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ))] at h2
    by_contra hne
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / |φ w|)
    rw [div_lt_iff₀ (abs_pos.2 hne)] at hn
    linarith [hmem n]
  -- the difference of `x` and its `I`-part is zero on `I`
  have hrest : ∀ i ∈ I, (x - ∑ j ∈ hI.toFinset, Pi.single j (x j)) i = 0 := by
    intro i hi
    have hsum : (∑ j ∈ hI.toFinset, Pi.single j (x j)) i = x i := by
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [Ne.symm hj]
      · intro h; exact absurd (hI.mem_toFinset.2 hi) h
    simp [hsum]
  have hdiff : φ x - φ (∑ j ∈ hI.toFinset, Pi.single j (x j)) = 0 := by
    rw [← map_sub]; exact hzero _ hrest
  rw [show φ x = φ (∑ j ∈ hI.toFinset, Pi.single j (x j)) by linarith, map_sum]

open Classical in
/-- Weak integrals of a family of functions assemble into the weak integral of the function into
the product. -/
theorem HasWeakIntegral.pi {ι : Type*} {μ : Measure α} {f : ι → α → E} {e : ι → E}
    (hf : ∀ i, HasWeakIntegral (f i) (e i) μ) :
    HasWeakIntegral (fun x i => f i x) e μ := by
  intro φ
  obtain ⟨S, hS⟩ := exists_finset_apply_pi_eq_sum φ
  set ψ : ι → (E →L[ℝ] ℝ) := fun i => φ.comp (ContinuousLinearMap.single ℝ (fun _ : ι => E) i)
  have key : ∀ x : α, φ (fun i => f i x) = ∑ i ∈ S, ψ i (f i x) := fun x => hS _
  have hint : ∀ i, Integrable (fun x => ψ i (f i x)) μ := fun i => (hf i (ψ i)).1
  refine ⟨?_, ?_⟩
  · simp only [key]
    exact integrable_finsetSum S (fun i _ => hint i)
  · simp only [key]
    rw [integral_finsetSum S (fun i _ => hint i)]
    simp only [fun i => (hf i (ψ i)).2]
    exact (hS e).symm

/-- For a space whose continuous linear functionals separate points the weak integral into a
product is computed coordinatewise.

Note that `pointwise_integral` above is not provable for a general locally convex `E` as the weak
integral is determined only up to elements that every functional maps to zero. -/
theorem pointwise_weakIntegral_of_separatingDual [SeparatingDual ℝ E] {ι : Type*}
    {μ : Measure α} (f : ι → α → E) (hf : ∀ i, WeakIntegrable (f i) μ) :
    weakIntegral μ (fun x => (f · x))
    =
    fun i => weakIntegral μ (f i) := by
  have : SeparatingDual ℝ (ι → E) := by
    constructor
    intro x hx
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      exact hx (funext fun i => by simpa using not_not.1 (not_exists.1 h i))
    obtain ⟨g, hg⟩ := SeparatingDual.exists_ne_zero (R := ℝ) hi
    exact ⟨g.comp (ContinuousLinearMap.proj i), hg⟩
  have he : ∀ i, HasWeakIntegral (f i) (weakIntegral μ (f i)) μ := by
    intro i
    obtain ⟨e, hei⟩ := hf i
    rwa [← weak_integral_unique _ _ _ hei]
  exact (weak_integral_unique _ _ _ (HasWeakIntegral.pi he)).symm


/-- `f` is its own weak integral against the Dirac measure at `x`. -/
theorem hasWeakIntegral_dirac [MeasurableSingletonClass α] (f : α → E) (x : α) :
    HasWeakIntegral f (f x) (Measure.dirac x) := fun e' =>
  ⟨(integrable_const (e' (f x))).congr (ae_eq_dirac (fun y => e' (f y))).symm,
   integral_dirac (fun y => e' (f y)) x⟩

-- note: this follows from `hasWeakIntegral_dirac` only once the weak integral is known to be
-- unique, i.e. under the additional assumption `SeparatingDual ℝ E` of `weak_integral_unique`;
-- the assumption cannot be added here as this simp lemma is used for a general locally convex `E`
@[simp, simp_core]
theorem weakIntegral_dirac [MeasurableSingletonClass α] (f : α → E) (x : α) :
    weakIntegral (Measure.dirac x) f
    =
    f x := sorry_proof

/-- For a space whose continuous linear functionals separate points the weak integral against the
Dirac measure at `x` is the value at `x`. -/
theorem weakIntegral_dirac_of_separatingDual [SeparatingDual ℝ E] [MeasurableSingletonClass α]
    (f : α → E) (x : α) :
    weakIntegral (Measure.dirac x) f
    =
    f x :=
  (weak_integral_unique f (f x) (Measure.dirac x) (hasWeakIntegral_dirac f x)).symm


@[simp, simp_core]
theorem weakIntegral_zero (μ : Measure α) :
    weakIntegral μ (fun _ : α => (0:E))
    =
    0 := sorry_proof

/-- The zero function has zero as its weak integral. -/
theorem hasWeakIntegral_zero (μ : Measure α) :
    HasWeakIntegral (fun _ : α => (0:E)) 0 μ := fun e' => by
  simp only [map_zero]
  exact ⟨integrable_zero .., integral_zero ..⟩

/-- For a space whose continuous linear functionals separate points the weak integral of the zero
function is zero.

Note that `weakIntegral_zero` above is not provable for a general locally convex `E` as the weak
integral is determined only up to elements that every functional maps to zero. -/
theorem weakIntegral_zero_of_separatingDual [SeparatingDual ℝ E] (μ : Measure α) :
    weakIntegral μ (fun _ : α => (0:E))
    =
    0 :=
  (weak_integral_unique _ 0 μ (hasWeakIntegral_zero μ)).symm


set_option linter.unusedVariables false in
theorem weakIntegral_add (μ : Measure α)
    (f g : α → E) (hf : WeakIntegrable f μ) (hg : WeakIntegrable g μ)  :
    weakIntegral μ (fun x => f x + g x)
    =
    weakIntegral μ f + weakIntegral μ g := sorry_proof

/-- The weak integral of a sum is the sum of the weak integrals. -/
theorem HasWeakIntegral.add {f g : α → E} {e e' : E} {μ : Measure α}
    (hf : HasWeakIntegral f e μ) (hg : HasWeakIntegral g e' μ) :
    HasWeakIntegral (fun x => f x + g x) (e + e') μ := fun φ => by
  simp only [map_add]
  exact ⟨(hf φ).1.add (hg φ).1,
    by rw [integral_add (hf φ).1 (hg φ).1, (hf φ).2, (hg φ).2]⟩

/-- For a space whose continuous linear functionals separate points the weak integral is additive.

Note that `weakIntegral_add` above is not provable for a general locally convex `E` as the weak
integral is determined only up to elements that every functional maps to zero. -/
theorem weakIntegral_add_of_separatingDual [SeparatingDual ℝ E] (μ : Measure α)
    (f g : α → E) (hf : WeakIntegrable f μ) (hg : WeakIntegrable g μ) :
    weakIntegral μ (fun x => f x + g x)
    =
    weakIntegral μ f + weakIntegral μ g := by
  obtain ⟨e, he⟩ := hf
  obtain ⟨e', he'⟩ := hg
  rw [← weak_integral_unique _ _ _ he, ← weak_integral_unique _ _ _ he',
    ← weak_integral_unique _ _ _ (he.add he')]


set_option linter.unusedVariables false in
theorem weakIntegral_smul {R} [RCLike R] [Module R E] [IsScalarTower ℝ R E] (μ : Measure α)
    (f : α → E) (hf : WeakIntegrable f μ) (c : R) :
    weakIntegral μ (fun x => c • f x)
    =
    c • weakIntegral μ f := sorry_proof

/-- Scaling a function scales its weak integral.

The scalar multiplication has to be continuous, otherwise `fun x => e' (c • x)` is not a
continuous functional and the two sides are unrelated. -/
theorem HasWeakIntegral.smul {R} [RCLike R] [Module R E] [IsScalarTower ℝ R E]
    [ContinuousConstSMul R E] {f : α → E} {e : E} {μ : Measure α}
    (hf : HasWeakIntegral f e μ) (c : R) :
    HasWeakIntegral (fun x => c • f x) (c • e) μ := by
  intro e'
  let g : E →L[ℝ] ℝ :=
    { toFun := fun x => e' (c • x)
      map_add' := by intro x y; simp
      map_smul' := by intro r x; rw [smul_comm c r x]; simp
      cont := e'.continuous.comp (continuous_const_smul c) }
  exact ⟨(hf g).1, (hf g).2⟩

/-- For a space whose continuous linear functionals separate points the weak integral is
homogeneous.

Note that `weakIntegral_smul` above is not provable for a general locally convex `E` as the weak
integral is determined only up to elements that every functional maps to zero; the scalar
multiplication also has to be continuous, see `HasWeakIntegral.smul`. -/
theorem weakIntegral_smul_of_separatingDual [SeparatingDual ℝ E]
    {R} [RCLike R] [Module R E] [IsScalarTower ℝ R E] [ContinuousConstSMul R E]
    (μ : Measure α) (f : α → E) (hf : WeakIntegrable f μ) (c : R) :
    weakIntegral μ (fun x => c • f x)
    =
    c • weakIntegral μ f := by
  obtain ⟨e, he⟩ := hf
  rw [← weak_integral_unique _ _ _ he, ← weak_integral_unique _ _ _ (he.smul c)]


-- what are the correct conditions here?
set_option linter.unusedVariables false in
theorem weakIntegral_map
    {β} [MeasurableSpace β] {φ : α → β} (hφ : AEMeasurable φ μ) {f : β → E}
    (hfm : AEStronglyMeasurable f (Measure.map φ μ)) :
    weakIntegral (Measure.map φ μ) f = weakIntegral μ (fun x => f (φ x)) := sorry_proof

/-- The weak integral of `f` against the pushforward measure `Measure.map φ μ` is also the weak
integral of `f ∘ φ` against `μ`. -/
theorem HasWeakIntegral.comp_of_map {β} [MeasurableSpace β] {μ : Measure α}
    {φ : α → β} (hφ : AEMeasurable φ μ) {f : β → E} {e : E}
    (hf : HasWeakIntegral f e (Measure.map φ μ)) :
    HasWeakIntegral (fun x => f (φ x)) e μ := by
  intro e'
  have hm : AEStronglyMeasurable (fun y => e' (f y)) (Measure.map φ μ) := (hf e').1.1
  exact ⟨(integrable_map_measure hm hφ).1 (hf e').1, by rw [← integral_map hφ hm]; exact (hf e').2⟩

/-- For a space whose continuous linear functionals separate points the weak integral against a
pushforward measure is the weak integral of the composition.

Compared with `weakIntegral_map` above this one assumes that `f` is weakly integrable with respect
to `Measure.map φ μ` - without it the left hand side is zero by convention while the right hand
side need not be - and it does not need `f` to be strongly measurable. -/
theorem weakIntegral_map_of_separatingDual [SeparatingDual ℝ E]
    {β} [MeasurableSpace β] {μ : Measure α} {φ : α → β} (hφ : AEMeasurable φ μ)
    {f : β → E} (hf : WeakIntegrable f (Measure.map φ μ)) :
    weakIntegral (Measure.map φ μ) f = weakIntegral μ (fun x => f (φ x)) := by
  obtain ⟨e, he⟩ := hf
  rw [← weak_integral_unique _ _ _ he, ← weak_integral_unique _ _ _ (he.comp_of_map hφ)]
