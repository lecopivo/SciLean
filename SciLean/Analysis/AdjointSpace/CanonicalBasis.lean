import SciLean.Analysis.AdjointSpace.Basic
import SciLean.Analysis.Normed.IsContinuousLinearMap
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
class CanonicalBasis (I : outParam $ Type v) (𝕜 : Type w) (X : Type u)
    [RCLike 𝕜] [NormedAddCommGroup X] [AdjointSpace 𝕜 X] [Fintype I]
  where
  /-- i-th basis vector -/
  basis (i : I) : X
  dualBasis (i : I) : X

  /-- projection of `x` onto i-th basis vector `basis i`

  Taking inner product with `dualBasis i` and calling `proj i` is equal on `FinVec ι K X` -/
  proj  (i : I) (x : X) : 𝕜
  dualProj (i : I) (x : X) : 𝕜

  basis_complete (x : X) : x = Finset.univ.sum (fun i : I => (proj i x) • basis i)

  basis_dualBasis (i j : I) : ⟪basis i, dualBasis i⟫[𝕜] = (if i = j then 1 else 0)
  proj_basis (i j : I) : proj i (basis i) = (if i = j then 1 else 0)
  dualProj_dualBasis (i j : I) : dualProj i (dualBasis i) = (if i = j then 1 else 0)

  proj_linear : ∀ i, IsContinuousLinearMap 𝕜 (proj i)
  dualProj_linear : ∀ i, IsContinuousLinearMap 𝕜 (dualProj i)

  -- not sure if these functions are useful, but might be at some point
  -- toDual (x : X) : X
  -- fromDual (x : X) : X

  -- toDual_basis (i : I) : (toDual (basis i)) = dualBasis i
  -- fromDual_dualBasis (x : X) (i : I) : fromDual (dualBasis i) = basis i

  -- toDual_linear : IsContinuousLinearMap 𝕜 toDual
  -- fromDual_linear : IsContinuousLinearMap 𝕜 fromDual

/-- `ⅇ[𝕜,X,i]` is the `i`-th basis vector of `X` over the field `𝕜` -/
macro "ⅇ[" k:term "," X:term "," i:term "]" : term => `(CanonicalBasis.basis $k (X:=$X) $i)
/-- `ⅇ[X,i]` is the `i`-th basis vector of `X` over the field currently set default field -/
macro "ⅇ[" X:term "," i:term "]" : term => `(CanonicalBasis.basis defaultScalar% (X:=$X) $i)
/-- `ⅇ[i]` is the `i`-th basis vector -/
macro "ⅇ[" i:term "]" : term => `(CanonicalBasis.basis defaultScalar% (X:=_) $i)

/-- `ⅇ[𝕜,X,i]` is the `i`-th basis vector of `X` over the field `𝕜` -/
macro "ⅇ'[" k:term "," X:term "," i:term "]" : term => `(CanonicalBasis.dualBasis $k (X:=$X) $i)
/-- `ⅇ[X,i]` is the `i`-th basis vector of `X` over the field currently set default field -/
macro "ⅇ'[" X:term "," i:term "]" : term => `(CanonicalBasis.dualBasis defaultScalar% (X:=$X) $i)
/-- `ⅇ[i]` is the `i`-th basis vector -/
macro "ⅇ'[" i:term "]" : term => `(CanonicalBasis.dualBasis defaultScalar% (X:=_) $i)

/-- `ℼ[𝕜,i]` is projection onto `i`-th basis vector over the field `𝕜` -/
macro "ℼ[" k:term "," i:term "]" : term => `(CanonicalBasis.proj (𝕜:=$k) $i)
/-- `ℼ[𝕜,i]` is projection onto `i`-th basis vector` -/
macro "ℼ[" i:term "]" : term => `(CanonicalBasis.proj (𝕜:=defaultScalar%) $i)

/-- `ℼ[𝕜,i]` is projection onto `i`-th basis vector over the field `𝕜` -/
macro "ℼ'[" k:term "," i:term "]" : term => `(CanonicalBasis.dualProj (𝕜:=$k) $i)
/-- `ℼ[𝕜,i]` is projection onto `i`-th basis vector` -/
macro "ℼ'[" i:term "]" : term => `(CanonicalBasis.dualProj (𝕜:=defaultScalar%) $i)

#exit
  /-- `ⅇ i` is the i-th basis vector -/
  prefix:max "ⅇ" => Basis.basis
  /-- `ⅇ[X] i` is the i-th basis vector of type `X` -/
  macro:max "ⅇ[" X:term "]" i:term : term => `(Basis.basis (X:=$X) $i)

  /-- `ⅇ' i` is the i-th dual basis vector -/
  prefix:max "ⅇ'" => DualBasis.dualBasis
  /-- `ⅇ'[X] i` is the i-th dual basis vector of type `X` -/
  macro:max "ⅇ'[" X:term "]" i:term : term => `(DualBasis.dualBasis (X:=$X) $i)

  /-- `ℼ i x` is projection of `x` onto i-th basis vector `ⅇ i` -/
  prefix:max "ℼ" => Basis.proj
  /-- `ℼ' i x` is projection of `x` onto i-th dual basis vector `ⅇ' i` -/
  prefix:max "ℼ'" => DualBasis.dualProj

  instance {X Y ι κ K} [Basis ι K X] [Basis κ K Y] [Zero X] [Zero Y] : Basis (ι ⊕ κ) K (X × Y)  where
    basis := λ i =>
      match i with
      | Sum.inl ix => (ⅇ ix, 0)
      | Sum.inr iy => (0, ⅇ iy)
    proj := λ i x =>
      match i with
      | Sum.inl ix => ℼ ix x.1
      | Sum.inr iy => ℼ iy x.2

  instance {X Y ι κ K} [DualBasis ι K X] [DualBasis κ K Y] [Zero X] [Zero Y] : DualBasis (ι ⊕ κ) K (X × Y) where
    dualBasis := λ i =>
      match i with
      | Sum.inl ix => (ⅇ' ix, 0)
      | Sum.inr iy => (0, ⅇ' iy)
    dualProj := λ i x =>
      match i with
      | Sum.inl ix => ℼ' ix x.1
      | Sum.inr iy => ℼ' iy x.2

  instance {X Y} [BasisDuality X] [BasisDuality Y] : BasisDuality (X×Y) where
    toDual := λ (x,y) => (BasisDuality.toDual x, BasisDuality.toDual y)
    fromDual := λ (x,y) => (BasisDuality.fromDual x, BasisDuality.fromDual y)

  instance {ι κ K X} [DecidableEq ι] [Basis κ K X] [Zero X] : Basis (ι×κ) K (ι → X) where
    basis := fun (i,j) i' => if i = i' then ⅇ j else 0
    proj := fun (i,j) x => ℼ j (x i)

  instance {ι κ K X} [DecidableEq ι] [DualBasis κ K X] [Zero X] : DualBasis (ι×κ) K (ι → X) where
    dualBasis := fun (i,j) i' => if i = i' then ⅇ' j else 0
    dualProj := fun (i,j) x => ℼ' j (x i)

  instance {ι X : Type _} [BasisDuality X] : BasisDuality (ι → X) where
    toDual := λ x i => BasisDuality.toDual (x i)
    fromDual := λ x i => BasisDuality.fromDual (x i)

  instance (priority:=high) {ι K : Type _} [DecidableEq ι] [RCLike K] : Basis ι K (ι → K) where
    basis := fun i j => if i = j then 1 else 0
    proj := fun i x => x i

  instance (priority:=high) {ι K : Type _} [DecidableEq ι] [RCLike K] : DualBasis ι K (ι → K) where
    dualBasis := fun i j => if i = j then 1 else 0
    dualProj := fun i x => x i

end Basis

/-- Predicate stating that the basis is orthonormal -/
class OrthonormalBasis (ι K X : Type _) [Semiring K] [Basis ι K X] [Inner K X] : Prop where
  is_orthogonal : ∀ i j, i ≠ j → ⟪ⅇ[X] i, ⅇ j⟫[K] = 0
  is_orthonormal : ∀ i, ⟪ⅇ[X] i, ⅇ i⟫[K] = 1

/-- Finite dimensional vector space over `K` with a basis indexed by `ι` -/
class FinVec (ι : outParam $ Type _) (K : Type _) (X : Type _) [outParam $ IndexType ι] [DecidableEq ι] [RCLike K] extends SemiHilbert K X, Basis ι K X, DualBasis ι K X, BasisDuality X where
  is_basis : ∀ x : X, x = ∑ i : ι, ℼ i x • ⅇ[X] i
  duality : ∀ i j, ⟪ⅇ[X] i, ⅇ'[X] j⟫[K] = if i=j then 1 else 0
  to_dual   : toDual   x = ∑ i,  ℼ i x • ⅇ'[X] i
  from_dual : fromDual x = ∑ i, ℼ' i x •  ⅇ[X] i


theorem basis_ext {ι K X} {_ : IndexType ι} [DecidableEq ι] [RCLike K] [FinVec ι K X] (x y : X)
  : (∀ i, ⟪x, ⅇ i⟫[K] = ⟪y, ⅇ i⟫[K]) → (x = y) := sorry_proof

theorem dualBasis_ext {ι K X} {_ : IndexType ι} [DecidableEq ι] [RCLike K] [FinVec ι K X] (x y : X)
  : (∀ i, ⟪x, ⅇ' i⟫[K] = ⟪y, ⅇ' i⟫[K]) → (x = y) := sorry_proof

theorem inner_proj_dualProj {ι K X} {_ : IndexType ι} [DecidableEq ι] [RCLike K] [FinVec ι K X] (x y : X)
  : ⟪x, y⟫[K] = ∑ i, ℼ i x * ℼ' i y :=
by
  calc
    ⟪x, y⟫[K] = ∑ i, ∑ j, ⟪(ℼ i x) • ⅇ[X] i, (ℼ' j y) • ⅇ' j⟫[K] := by sorry_proof -- rw[← (FinVec.is_basis x), ← (FinVec.is_basis y)]
         _ = ∑ i, ∑ j, (ℼ i x * ℼ' j y) * ⟪ⅇ[X] i, ⅇ' j⟫[K] := by sorry_proof -- use linearity of the sum
         _ = ∑ i, ∑ j, (ℼ i x * ℼ' j y) * if i=j then 1 else 0 := by simp [FinVec.duality]
         _ = ∑ i, ℼ i x * ℼ' i y := sorry_proof -- summing over [[i=j]]

variable {ι K X} [IndexType ι] [DecidableEq ι] [RCLike K] [FinVec ι K X]


namespace FinVec
scoped instance (priority:=low) : GetElem X ι K (fun _ _ => True) where
  getElem x i _ := ℼ i x

scoped instance (priority:=low) : GetElem X ℕ K (fun _ i => i < size ι) where
  getElem x i h := ℼ (IndexType.fromFin ⟨i,h⟩) x
end FinVec

@[simp]
theorem inner_basis_dualBasis (i j : ι)
  : ⟪ⅇ[X] i, ⅇ' j⟫[K] = if i=j then 1 else 0 :=
by apply FinVec.duality

@[simp]
theorem inner_dualBasis_basis  (i j : ι)
  : ⟪ⅇ'[X] i, ⅇ j⟫[K] = if i=j then 1 else 0 :=
by sorry_proof

@[simp]
theorem inner_dualBasis_proj  (i : ι) (x : X)
  : ⟪x, ⅇ' i⟫[K] = ℼ i x :=
by sorry_proof
  -- calc
  --   ⟪x, ⅇ' i⟫[K] = ⟪∑ j, ℼ j x • ⅇ[X] j, ⅇ' i⟫[K] := by sorry_proof -- rw[← (FinVec.is_basis x)]
  --           _ = ∑ j, ℼ j x * if j=i then 1 else 0 := by sorry_proof -- inner_basis_dualBasis and some linearity
  --           _ = ℼ i x := by sorry_proof

@[simp]
theorem inner_basis_dualProj (i : ι) (x : X)
  : ⟪x, ⅇ i⟫[K] = ℼ' i x :=
by sorry_proof

@[simp]
theorem proj_basis (i j : ι)
  : ℼ i (ⅇ[X] j) = if i=j then 1 else 0 :=
by simp only [←inner_dualBasis_proj, inner_basis_dualBasis, eq_comm]

@[simp]
theorem proj_zero (i : ι)
  : ℼ i (0 : X) = 0 :=
by sorry_proof

@[simp]
theorem dualProj_dualBasis (i j : ι)
  : ℼ' i (ⅇ'[X] j) = if i=j then 1 else 0 :=
by simp only [←inner_basis_dualProj, inner_dualBasis_basis, eq_comm]

instance : FinVec Unit K K where
  is_basis := by simp[Basis.proj, Basis.basis]; sorry_proof
  duality := by simp[Basis.proj, Basis.basis, DualBasis.dualProj, DualBasis.dualBasis, Inner.inner]
  to_dual := by sorry_proof
  from_dual := by sorry_proof

instance : OrthonormalBasis Unit K K where
  is_orthogonal  := sorry_proof
  is_orthonormal := sorry_proof

-- @[infer_tc_goals_rl]
instance {ι κ K X Y}
    [IndexType ι] [DecidableEq ι]
    [IndexType κ] [DecidableEq κ]
    [RCLike K] [FinVec ι K X] [FinVec κ K Y] :
    FinVec (ι⊕κ) K (X×Y) where
  is_basis := sorry_proof
  duality := sorry_proof
  to_dual := sorry_proof
  from_dual := sorry_proof

instance
    [IndexType ι] [DecidableEq ι]
    [IndexType κ] [DecidableEq κ]
    [FinVec ι K X] [OrthonormalBasis ι K X]
    [FinVec κ K Y] [OrthonormalBasis κ K Y] :
    OrthonormalBasis (ι⊕κ) K (X×Y) where
  is_orthogonal  := by simp[Inner.inner, Basis.basis]; sorry_proof
  is_orthonormal := by simp[Inner.inner, Basis.basis]; sorry_proof


-- this might require `FinVec` instance, without it we probably do not know that `⟪0,x⟫ = 0`
instance [IndexType ι] [IndexType κ] [Zero X] [Basis κ K X] [OrthonormalBasis κ K X] : OrthonormalBasis (ι×κ) K (ι → X) where
  is_orthogonal  := by simp[Inner.inner, Basis.basis]; sorry_proof
  is_orthonormal := by simp[Inner.inner, Basis.basis]; sorry_proof


instance (priority:=high) {ι : Type} {K : Type v} [IndexType ι] [DecidableEq ι] [RCLike K]
  : FinVec ι K (ι → K) where
  is_basis := sorry_proof
  duality := sorry_proof
  to_dual := sorry_proof
  from_dual := sorry_proof

instance {ι κ : Type} {K X : Type _} [IndexType ι] [IndexType κ] [DecidableEq ι] [DecidableEq κ] [RCLike K] [FinVec κ K X]
  : FinVec (ι×κ) K (ι → X) where
  is_basis := sorry_proof
  duality := sorry_proof
  to_dual := sorry_proof
  from_dual := sorry_proof
