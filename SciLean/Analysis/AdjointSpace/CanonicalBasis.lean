module

public import SciLean.Analysis.AdjointSpace.Basic
public import SciLean.Analysis.Normed.IsContinuousLinearMap

@[expose] public section

-- import SciLean.Data

open ComplexConjugate

namespace SciLean

open Classical in
/-- Canonical basis `ⅇ i` on space `X` over the field `𝕜` indexed by `i : I`

We do not require orthonormality, thus it comes with dual basis `ⅇ'` such that
```
  ⟪ⅇ i, ⅇ' j⟫ = if
```
-/
class CanonicalBasis (I : outParam Type*) (𝕜 X : Type*) [RCLike 𝕜]
      [NormedAddCommGroup X] [AdjointSpace 𝕜 X] [Fintype I]
  where
  /-- `ⅇ[i]` is `i`-th basis vector of a vector space

  Can be also written a `ⅇ[𝕜,X,i]` or `ⅇ[X,i]` to specify the vector space `X` and base field `𝕜`

  To project a vector on this basis vector use `ℼ[i]` which notation for `proj i` -/
  basis (i : I) : X
  /-- `ⅇ'[i]` is `i`-th dual basis vector of a vector space

  Can be also written a `ⅇ'[𝕜,X,i]` or `ⅇ'[X,i]` to specify the vector space `X` and base field `𝕜`

  To project a vector on this basis vector use `ℼ'[i]` which notation for `dualProj i`

  We have `dualBasis` because the basis `ⅇ[i]` is not necessarily orthonormal, but similar condition
  holds between `ⅇ[i]` and `ⅇ'[j]`
  ```
    ⟪e[i], ⅇ'[j]⟫ = if i = j then 1 else 0
  ```
  -/
  dualBasis (i : I) : X
  /--
  `ℼ[𝕜,i]` is the projection onto i-th basis vector.

  Can be also written a `ℼ[𝕜,i]` to specify the base field `𝕜`
  -/
  proj  (i : I) (x : X) : 𝕜
  /--
  `ℼ[𝕜,i]` is the projection onto i-th dual basis vector.

  Can be also written a `ℼ'[𝕜,i]` to specify the base field `𝕜`
  -/
  dualProj (i : I) (x : X) : 𝕜

  basis_complete (x : X) : x = Finset.univ.sum (fun i : I => proj i x • basis i)

  proj_basis (i j : I) : proj i (basis j) = if i = j then 1 else 0
  dualProj_dualBasis (i j : I) : dualProj i (dualBasis j) = if i = j then 1 else 0
  inner_basis_dualBasis (i j : I) : ⟪basis i, dualBasis j⟫[𝕜] = if i = j then 1 else 0

  proj_linear : ∀ i, IsContinuousLinearMap 𝕜 (proj i)
  dualProj_linear : ∀ i, IsContinuousLinearMap 𝕜 (dualProj i)


----------------------------------------------------------------------------------------------------
-- Notation ----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[inherit_doc CanonicalBasis.basis]
macro:max "ⅇ[" k:term ", " X:term ", " i:term  "]" : term =>
  `(CanonicalBasis.basis (𝕜:=$k) (X:=$X) $i)

@[inherit_doc CanonicalBasis.basis]
macro:max "ⅇ[" X:term ", " i:term  "]" : term =>
  `(CanonicalBasis.basis (𝕜:=defaultScalar%) (X:=$X) $i)

@[inherit_doc CanonicalBasis.basis]
macro:max "ⅇ[" i:term  "]" : term =>
  `(CanonicalBasis.basis (𝕜:=defaultScalar%) (X:=_) $i)


@[inherit_doc CanonicalBasis.dualBasis]
macro:max "ⅇ'[" k:term ", " X:term ", " i:term  "]" : term =>
  `(CanonicalBasis.dualBasis (𝕜:=$k) (X:=$X) $i)

@[inherit_doc CanonicalBasis.dualBasis]
macro:max "ⅇ'[" X:term ", " i:term  "]" : term =>
  `(CanonicalBasis.dualBasis (𝕜:=defaultScalar%) (X:=$X) $i)

@[inherit_doc CanonicalBasis.dualBasis]
macro:max "ⅇ'[" i:term  "]" : term =>
  `(CanonicalBasis.dualBasis (𝕜:=defaultScalar%) (X:=_) $i)


@[inherit_doc CanonicalBasis.proj]
macro:max "ℼ[" k:term ", " i:term  "]" : term =>
  `(CanonicalBasis.proj (𝕜:=$k) $i)

@[inherit_doc CanonicalBasis.proj]
macro:max "ℼ[" i:term  "]" : term =>
  `(CanonicalBasis.proj (𝕜:=defaultScalar%) $i)


@[inherit_doc CanonicalBasis.proj]
macro:max "ℼ'[" k:term ", " i:term  "]" : term =>
  `(CanonicalBasis.dualProj (𝕜:=$k) $i)

@[inherit_doc CanonicalBasis.proj]
macro:max "ℼ'[" i:term  "]" : term =>
  `(CanonicalBasis.dualProj (𝕜:=defaultScalar%) $i)



----------------------------------------------------------------------------------------------------
-- Baisc Instances  --------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

instance {𝕜} [RCLike 𝕜] : CanonicalBasis Unit 𝕜 𝕜
  where
  basis _ := 1
  dualBasis _ := 1
  proj _ x := x
  dualProj _ x := x
  basis_complete := by simp
  proj_basis := by simp
  dualProj_dualBasis := by simp
  inner_basis_dualBasis := by simp
  proj_linear := by intro i; fun_prop
  dualProj_linear := by intro i; fun_prop


-- Prod
instance {𝕜} [RCLike 𝕜]
    {X : Type*} [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
    {I : Type*} [Fintype I] [CanonicalBasis I 𝕜 X]
    {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
    {J : Type*} [Fintype J] [CanonicalBasis J 𝕜 Y] :
    CanonicalBasis (I ⊕ J) 𝕜 (X×Y)
  where
  basis i :=
    match i with
    | .inl i => (ⅇ[𝕜,X,i],0)
    | .inr j => (0,ⅇ[𝕜,Y,j])
  dualBasis i :=
    match i with
    | .inl i => (ⅇ'[𝕜,X,i],0)
    | .inr j => (0,ⅇ'[𝕜,Y,j])
  proj i x :=
    match i with
    | .inl i => ℼ[𝕜,i] x.1
    | .inr j => ℼ[𝕜,j] x.2
  dualProj i x :=
    match i with
    | .inl i => ℼ'[𝕜,i] x.1
    | .inr j => ℼ'[𝕜,j] x.2

  basis_complete := by
    intro x
    rw [Fintype.sum_sum_type]
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, smul_zero, Finset.sum_const_zero,
        add_zero]
      exact CanonicalBasis.basis_complete (𝕜:=𝕜) (X:=X) x.1
    · simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, smul_zero, Finset.sum_const_zero,
        zero_add]
      exact CanonicalBasis.basis_complete (𝕜:=𝕜) (X:=Y) x.2
  proj_basis := by
    rintro (i|i) (j|j)
    · rcases eq_or_ne i j with rfl | h
      · simp [CanonicalBasis.proj_basis (𝕜:=𝕜) (X:=X)]
      · simp [CanonicalBasis.proj_basis (𝕜:=𝕜) (X:=X), h, Sum.inl_injective.ne h]
    · simpa using (CanonicalBasis.proj_linear (𝕜:=𝕜) (X:=X) i).1.map_zero
    · simpa using (CanonicalBasis.proj_linear (𝕜:=𝕜) (X:=Y) i).1.map_zero
    · rcases eq_or_ne i j with rfl | h
      · simp [CanonicalBasis.proj_basis (𝕜:=𝕜) (X:=Y)]
      · simp [CanonicalBasis.proj_basis (𝕜:=𝕜) (X:=Y), h, Sum.inr_injective.ne h]
  dualProj_dualBasis := by
    rintro (i|i) (j|j)
    · rcases eq_or_ne i j with rfl | h
      · simp [CanonicalBasis.dualProj_dualBasis (𝕜:=𝕜) (X:=X)]
      · simp [CanonicalBasis.dualProj_dualBasis (𝕜:=𝕜) (X:=X), h, Sum.inl_injective.ne h]
    · simpa using (CanonicalBasis.dualProj_linear (𝕜:=𝕜) (X:=X) i).1.map_zero
    · simpa using (CanonicalBasis.dualProj_linear (𝕜:=𝕜) (X:=Y) i).1.map_zero
    · rcases eq_or_ne i j with rfl | h
      · simp [CanonicalBasis.dualProj_dualBasis (𝕜:=𝕜) (X:=Y)]
      · simp [CanonicalBasis.dualProj_dualBasis (𝕜:=𝕜) (X:=Y), h, Sum.inr_injective.ne h]
  inner_basis_dualBasis := by
    rintro (i|i) (j|j)
    · rcases eq_or_ne i j with rfl | h
      · simp [AdjointSpace.inner_prod_split, CanonicalBasis.inner_basis_dualBasis (𝕜:=𝕜) (X:=X)]
      · simp [AdjointSpace.inner_prod_split, CanonicalBasis.inner_basis_dualBasis (𝕜:=𝕜) (X:=X),
              h, Sum.inl_injective.ne h]
    · simp [AdjointSpace.inner_prod_split]
    · simp [AdjointSpace.inner_prod_split]
    · rcases eq_or_ne i j with rfl | h
      · simp [AdjointSpace.inner_prod_split, CanonicalBasis.inner_basis_dualBasis (𝕜:=𝕜) (X:=Y)]
      · simp [AdjointSpace.inner_prod_split, CanonicalBasis.inner_basis_dualBasis (𝕜:=𝕜) (X:=Y),
              h, Sum.inr_injective.ne h]
  proj_linear := by
    rintro (i|j) <;> constructor
    · constructor
      · intro x y; exact (CanonicalBasis.proj_linear i).1.map_add _ _
      · intro c x; exact (CanonicalBasis.proj_linear i).1.map_smul _ _
    · exact (CanonicalBasis.proj_linear i).2.comp continuous_fst
    · constructor
      · intro x y; exact (CanonicalBasis.proj_linear j).1.map_add _ _
      · intro c x; exact (CanonicalBasis.proj_linear j).1.map_smul _ _
    · exact (CanonicalBasis.proj_linear j).2.comp continuous_snd
  dualProj_linear := by
    rintro (i|j) <;> constructor
    · constructor
      · intro x y; exact (CanonicalBasis.dualProj_linear i).1.map_add _ _
      · intro c x; exact (CanonicalBasis.dualProj_linear i).1.map_smul _ _
    · exact (CanonicalBasis.dualProj_linear i).2.comp continuous_fst
    · constructor
      · intro x y; exact (CanonicalBasis.dualProj_linear j).1.map_add _ _
      · intro c x; exact (CanonicalBasis.dualProj_linear j).1.map_smul _ _
    · exact (CanonicalBasis.dualProj_linear j).2.comp continuous_snd

-- Pi
instance {𝕜} [RCLike 𝕜]
    {X : Type*} [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
    {I : Type*} [Fintype I] [CanonicalBasis I 𝕜 X]
    {J : Type*} {nJ} [IndexType J nJ] [Fold J] [DecidableEq J] :
    CanonicalBasis (J × I) 𝕜 (J → X)
  where
  basis := fun (j,i) => fun j' => if j' = j then ⅇ[𝕜,X,i] else 0
  dualBasis := fun (j,i) => fun j' => if j' = j then ⅇ'[𝕜,X,i] else 0
  proj := fun (j,i) x => ℼ[𝕜,i] (x j)
  dualProj := fun (j,i) x => ℼ'[𝕜,i] (x j)

  basis_complete := by
    intro x
    funext j'
    rw [Fintype.sum_prod_type, Finset.sum_apply]
    have h : ∀ j : J, (∑ i : I, (CanonicalBasis.proj (𝕜:=𝕜) i (x j)) •
          (fun j'' => if j'' = j then (ⅇ[𝕜,X,i]) else 0)) j' = if j' = j then x j' else 0 := by
      intro j
      rw [Finset.sum_apply]
      by_cases hj : j' = j
      · subst hj
        simp only [Pi.smul_apply, ite_true]
        exact (CanonicalBasis.basis_complete (𝕜:=𝕜) (X:=X) (x j')).symm
      · simp [hj]
    simp only [h]
    simp
  proj_basis := by
    rintro ⟨j,i⟩ ⟨j',i'⟩
    by_cases hj : j = j'
    · subst hj
      rcases eq_or_ne i i' with rfl | hi
      · simp [CanonicalBasis.proj_basis (𝕜:=𝕜) (X:=X)]
      · simp [CanonicalBasis.proj_basis (𝕜:=𝕜) (X:=X), hi, Prod.ext_iff]
    · simp [hj, (CanonicalBasis.proj_linear (𝕜:=𝕜) (X:=X) i).1.map_zero, Prod.ext_iff]
  dualProj_dualBasis := by
    rintro ⟨j,i⟩ ⟨j',i'⟩
    by_cases hj : j = j'
    · subst hj
      rcases eq_or_ne i i' with rfl | hi
      · simp [CanonicalBasis.dualProj_dualBasis (𝕜:=𝕜) (X:=X)]
      · simp [CanonicalBasis.dualProj_dualBasis (𝕜:=𝕜) (X:=X), hi, Prod.ext_iff]
    · simp [hj, (CanonicalBasis.dualProj_linear (𝕜:=𝕜) (X:=X) i).1.map_zero, Prod.ext_iff]
  inner_basis_dualBasis := by
    rintro ⟨j,i⟩ ⟨j',i'⟩
    rw [AdjointSpace.inner_forall_split, IndexType.sum_eq_finset_sum]
    by_cases hj : j = j'
    · subst hj
      refine (Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)).trans ?_
      rcases eq_or_ne i i' with rfl | hi
      · simp [CanonicalBasis.inner_basis_dualBasis (𝕜:=𝕜) (X:=X)]
      · simp [CanonicalBasis.inner_basis_dualBasis (𝕜:=𝕜) (X:=X), hi, Prod.ext_iff]
    · refine (Finset.sum_eq_zero ?_).trans ?_
      · intro b _
        by_cases hb : b = j <;> simp [hb, hj]
      · simp [hj, Prod.ext_iff]
  proj_linear := by
    rintro ⟨j,i⟩
    constructor
    · constructor
      · intro x y; exact (CanonicalBasis.proj_linear i).1.map_add _ _
      · intro c x; exact (CanonicalBasis.proj_linear i).1.map_smul _ _
    · exact (CanonicalBasis.proj_linear i).2.comp (continuous_apply j)
  dualProj_linear := by
    rintro ⟨j,i⟩
    constructor
    · constructor
      · intro x y; exact (CanonicalBasis.dualProj_linear i).1.map_add _ _
      · intro c x; exact (CanonicalBasis.dualProj_linear i).1.map_smul _ _
    · exact (CanonicalBasis.dualProj_linear i).2.comp (continuous_apply j)


-- The original version of `CanonicalBasis.ofEquiv` transported the basis along a bare equivalence
-- `g : X ≃ Y`. None of the `CanonicalBasis` laws can be established for such `g` - already
-- `basis_complete` needs `g` to be linear and `inner_basis_dualBasis` needs `g` to preserve the
-- inner product - so it is kept here only for reference and superseded by the version below.
--
-- @[instance_reducible]
-- def CanonicalBasis.ofEquiv
--     {J : Type*} (I : Type*) {Y : Type*} (X : Type*)
--     {𝕜 : Type*} [RCLike 𝕜]
--     [Fintype I] [Fintype J]
--     [NormedAddCommGroup X] [AdjointSpace 𝕜 X] [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
--     [CanonicalBasis I 𝕜 X]
--     (f : I ≃ J) (g : X ≃ Y) : CanonicalBasis J 𝕜 Y where
--   basis j := g ⅇ[𝕜,X, f.symm j]
--   dualBasis j := g ⅇ'[𝕜,X, f.symm j]
--   proj j y := ℼ[𝕜,f.symm j] (g.symm y)
--   dualProj j y := ℼ'[𝕜,f.symm j] (g.symm y)
--
--   basis_complete := sorry_proof
--   proj_basis := sorry_proof
--   dualProj_dualBasis := sorry_proof
--   inner_basis_dualBasis := sorry_proof
--   proj_linear := sorry_proof
--   dualProj_linear := sorry_proof

open Classical in
/-- Transport a canonical basis along a reindexing `f : I ≃ J` and a continuous linear
equivalence `g : X ≃L[𝕜] Y` that preserves the inner product. -/
@[instance_reducible]
def CanonicalBasis.ofEquiv
    {J : Type*} (I : Type*) {Y : Type*} (X : Type*)
    {𝕜 : Type*} [RCLike 𝕜]
    [Fintype I] [Fintype J]
    [NormedAddCommGroup X] [AdjointSpace 𝕜 X] [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
    [CanonicalBasis I 𝕜 X]
    (f : I ≃ J) (g : X ≃L[𝕜] Y)
    (hg : ∀ x x' : X, ⟪g x, g x'⟫[𝕜] = ⟪x, x'⟫[𝕜]) : CanonicalBasis J 𝕜 Y where
  basis j := g ⅇ[𝕜,X, f.symm j]
  dualBasis j := g ⅇ'[𝕜,X, f.symm j]
  proj j y := ℼ[𝕜,f.symm j] (g.symm y)
  dualProj j y := ℼ'[𝕜,f.symm j] (g.symm y)

  basis_complete := by
    intro y
    conv_lhs => rw [show y = g (g.symm y) from (g.apply_symm_apply y).symm]
    conv_lhs => rw [CanonicalBasis.basis_complete (𝕜:=𝕜) (I:=I) (g.symm y)]
    rw [map_sum]
    simp only [map_smul]
    exact (Equiv.sum_comp f.symm
      (fun i => CanonicalBasis.proj (𝕜:=𝕜) i (g.symm y) • g ⅇ[𝕜,X,i])).symm
  proj_basis := by
    intro j j'
    rw [ContinuousLinearEquiv.symm_apply_apply, CanonicalBasis.proj_basis]
    simp [f.symm.injective.eq_iff]
  dualProj_dualBasis := by
    intro j j'
    rw [ContinuousLinearEquiv.symm_apply_apply, CanonicalBasis.dualProj_dualBasis]
    simp [f.symm.injective.eq_iff]
  inner_basis_dualBasis := by
    intro j j'
    rw [hg, CanonicalBasis.inner_basis_dualBasis]
    simp [f.symm.injective.eq_iff]
  proj_linear := by
    intro j
    constructor
    · constructor
      · intro x y; simp [(CanonicalBasis.proj_linear (𝕜:=𝕜) (X:=X) (f.symm j)).1.map_add]
      · intro c x; simp [(CanonicalBasis.proj_linear (𝕜:=𝕜) (X:=X) (f.symm j)).1.map_smul]
    · exact (CanonicalBasis.proj_linear (𝕜:=𝕜) (X:=X) (f.symm j)).2.comp g.symm.continuous
  dualProj_linear := by
    intro j
    constructor
    · constructor
      · intro x y; simp [(CanonicalBasis.dualProj_linear (𝕜:=𝕜) (X:=X) (f.symm j)).1.map_add]
      · intro c x; simp [(CanonicalBasis.dualProj_linear (𝕜:=𝕜) (X:=X) (f.symm j)).1.map_smul]
    · exact (CanonicalBasis.dualProj_linear (𝕜:=𝕜) (X:=X) (f.symm j)).2.comp g.symm.continuous

----------------------------------------------------------------------------------------------------
-- Baisc Theorems  ---------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


variable
  {I : Type*} [Fintype I]
  {𝕜 : Type*} [RCLike 𝕜]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
  [CanonicalBasis I 𝕜 X]

set_default_scalar 𝕜


variable (𝕜) in
theorem basis_ext {x y : X} :
  (∀ (i : I), ⟪x, ⅇ[i]⟫ = ⟪y, ⅇ[i]⟫) → (x = y) := by
  intro h
  apply AdjointSpace.ext_inner_right 𝕜
  intro v
  conv_lhs => rw [CanonicalBasis.basis_complete (𝕜:=𝕜) (I:=I) v]
  conv_rhs => rw [CanonicalBasis.basis_complete (𝕜:=𝕜) (I:=I) v]
  rw [AdjointSpace.inner_sum, AdjointSpace.inner_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [AdjointSpace.inner_smul_right, AdjointSpace.inner_smul_right, h i]

variable (I 𝕜) in
theorem dualBasis_ext {x y : X} :
  (∀ (i : I), ⟪x, ⅇ'[i]⟫ = ⟪y, ⅇ'[i]⟫) → (x = y) := by
  intro h
  classical
  have hz : ∀ i : I, ℼ[𝕜,i] (x - y) = 0 := by
    intro i
    have h0 : ⟪x - y, ⅇ'[𝕜,X,i]⟫[𝕜] = 0 := by
      rw [AdjointSpace.inner_sub_left, h i, sub_self]
    rw [CanonicalBasis.basis_complete (𝕜:=𝕜) (I:=I) (x-y), AdjointSpace.sum_inner] at h0
    simp only [AdjointSpace.inner_smul_left, CanonicalBasis.inner_basis_dualBasis, mul_ite,
      mul_one, mul_zero] at h0
    simpa using h0
  have hxy : x - y = 0 := by
    conv_lhs => rw [CanonicalBasis.basis_complete (𝕜:=𝕜) (I:=I) (x-y)]
    simp [hz]
  exact sub_eq_zero.mp hxy

-- This statement is false over a complex field: the inner product is conjugate linear in its
-- first argument, so the projections of `x` have to be conjugated. For `𝕜 = X = ℂ`, `I = Unit`,
-- `x = y = Complex.I` it claims `1 = -1`. The corrected statement is proved at the end of this
-- file, under the same name.
-- theorem inner_eq_sum_proj_dualProj (x y : X)
--   : ⟪x, y⟫ = ∑ (i : I), ℼ[i] x * ℼ'[i] y :=
-- by
--   classical
--   calc
--     ⟪x, y⟫ = ∑ i, ∑ j, ⟪(ℼ[i] x) • ⅇ[X,i], (ℼ'[j] y) • ⅇ'[j]⟫ := by sorry_proof
--          _ = ∑ i, ∑ j, (ℼ[i] x * ℼ'[j] y) * ⟪ⅇ[X,i], ⅇ'[j]⟫ := by sorry_proof -- use linearity of the sum
--          _ = ∑ i, ∑ j, (ℼ[i] x * ℼ'[j] y) * if i=j then 1 else 0 := by sorry_proof
--          _ = ∑ i, ℼ[i] x * ℼ'[i] y := by simp -- summing over [[i=j]]


@[simp, simp_core]
theorem inner_basis_dualBasis [DecidableEq I] (i j : I) :
    ⟪ⅇ[X,i], ⅇ'[j]⟫ = if i=j then 1 else 0 := by
  simp[CanonicalBasis.inner_basis_dualBasis]

@[simp, simp_core]
theorem inner_dualBasis_basis [DecidableEq I] (i j : I) :
    ⟪ⅇ'[X,i], ⅇ[j]⟫ = if i=j then 1 else 0 := by
  rw [← AdjointSpace.inner_conj_symm, CanonicalBasis.inner_basis_dualBasis]
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [h, Ne.symm h]

@[simp, simp_core]
theorem proj_basis [DecidableEq I] (i j : I) :
    ℼ[i] ⅇ[X,j] = if i=j then 1 else 0 := by
  simp[CanonicalBasis.proj_basis]

@[simp, simp_core]
theorem dualProj_dualBasis [DecidableEq I] (i j : I) :
    ℼ'[i] ⅇ'[X,j] = if i=j then 1 else 0 := by
  simp[CanonicalBasis.dualProj_dualBasis]


@[fun_prop]
theorem CanonicalBasis.proj.arg_x.IsLinearMap_rule (i : I) :
  IsLinearMap 𝕜 (fun x : X => ℼ[i] x) := (CanonicalBasis.proj_linear i).1

@[fun_prop]
theorem CanonicalBasis.proj.arg_x.IsContinuousLinearMap_rule (i : I) :
  IsContinuousLinearMap 𝕜 (fun x : X => ℼ[i] x) := CanonicalBasis.proj_linear i

#generate_linear_map_simps CanonicalBasis.proj.arg_x.IsLinearMap_rule


@[fun_prop]
theorem CanonicalBasis.dualProj.arg_x.IsLinearMap_rule (i : I) :
  IsLinearMap 𝕜 (fun x : X => ℼ'[i] x) := (CanonicalBasis.dualProj_linear i).1

@[fun_prop]
theorem CanonicalBasis.dualProj.arg_x.IsContinuousLinearMap_rule (i : I) :
  IsContinuousLinearMap 𝕜 (fun x : X => ℼ'[i] x) := CanonicalBasis.dualProj_linear i

#generate_linear_map_simps CanonicalBasis.dualProj.arg_x.IsLinearMap_rule


-- TODO: remove `IndexType`
-- This statement is false over a complex field: for `𝕜 = X = ℂ`, `I = Unit` and `x = Complex.I`
-- it claims `-Complex.I = Complex.I`. The corrected statement, with the projection conjugated,
-- is proved at the end of this file under the same name.
-- @[simp]
-- theorem inner_dualBasis_right_eq_proj (i : I) (x : X) :
--     ⟪x, ⅇ'[i]⟫ = ℼ[i] x := by
--   classical
--   calc
--     ⟪x, ⅇ'[i]⟫ = ⟪∑ j, ℼ[j] x • ⅇ[X,j], ⅇ'[X,i]⟫ := by sorry_proof
--             _ = ∑ j, ℼ[j] x * if j=i then 1 else 0 := by sorry_proof
--             _ = ℼ[i] x := by simp

@[simp]
theorem inner_dualBasis_left_eq_proj (i : I) (x : X) :
    ⟪ⅇ'[i], x⟫ = ℼ[i] x := by
  classical
  conv_lhs => rw [CanonicalBasis.basis_complete (𝕜:=𝕜) (I:=I) x]
  rw [AdjointSpace.inner_sum]
  simp only [AdjointSpace.inner_smul_right, inner_dualBasis_basis]
  simp

-- This statement is false over a complex field, see the comment at `inner_dualBasis_right_eq_proj`.
-- The corrected statement is proved at the end of this file under the same name.
-- @[simp]
-- theorem inner_basis_right_eq_dualProj (i : I) (x : X) :
--     ⟪x, ⅇ[i]⟫ = ℼ'[i] x := by sorry_proof

@[simp]
theorem inner_basis_left_eq_dualProj (i : I) (x : X) :
    ⟪ⅇ[i], x⟫ = ℼ'[i] x := by
  classical
  have hlin := (CanonicalBasis.dualProj_linear (𝕜:=𝕜) (X:=X) i).1
  have hx : x = ∑ j : I, ⟪ⅇ[𝕜,X,j], x⟫[𝕜] • ⅇ'[𝕜,X,j] := by
    apply basis_ext 𝕜
    intro j
    rw [AdjointSpace.sum_inner]
    have h : ∀ b : I, ⟪⟪ⅇ[𝕜,X,b], x⟫[𝕜] • ⅇ'[𝕜,X,b], ⅇ[𝕜,X,j]⟫[𝕜]
             = if b = j then ⟪x, ⅇ[𝕜,X,j]⟫[𝕜] else 0 := by
      intro b
      rw [AdjointSpace.inner_smul_left, inner_dualBasis_basis]
      rcases eq_or_ne b j with rfl | hb
      · simp [AdjointSpace.inner_conj_symm]
      · simp [hb]
    simp only [h]
    simp
  conv_rhs => rw [hx]
  rw [show (ℼ'[𝕜,i] : X → 𝕜) = ⇑(IsLinearMap.mk' _ hlin) from rfl, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp


/-- Corrected version of `inner_dualBasis_right_eq_proj`: the inner product is conjugate linear
in its first argument, hence the projection gets conjugated. -/
@[simp]
theorem inner_dualBasis_right_eq_proj (i : I) (x : X) :
    ⟪x, ⅇ'[i]⟫ = conj (ℼ[i] x) := by
  rw [← AdjointSpace.inner_conj_symm, inner_dualBasis_left_eq_proj]

/-- Corrected version of `inner_basis_right_eq_dualProj`: the inner product is conjugate linear
in its first argument, hence the projection gets conjugated. -/
@[simp]
theorem inner_basis_right_eq_dualProj (i : I) (x : X) :
    ⟪x, ⅇ[i]⟫ = conj (ℼ'[i] x) := by
  rw [← AdjointSpace.inner_conj_symm, inner_basis_left_eq_dualProj]

/-- Corrected version of `inner_eq_sum_proj_dualProj`: the inner product is conjugate linear
in its first argument, hence the projections of `x` get conjugated. -/
theorem inner_eq_sum_proj_dualProj (x y : X) :
    ⟪x, y⟫ = ∑ (i : I), conj (ℼ[i] x) * ℼ'[i] y := by
  conv_lhs => rw [CanonicalBasis.basis_complete (𝕜:=𝕜) (I:=I) x]
  rw [AdjointSpace.sum_inner]
  exact Finset.sum_congr rfl fun i _ => by
    rw [AdjointSpace.inner_smul_left, inner_basis_left_eq_dualProj]
