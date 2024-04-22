import LeanColls
import SciLean.Core.Objects.SemiInnerProductSpace

open ComplexConjugate
open LeanColls

namespace SciLean

/-- Basis of the space `X` over the field `K` indexed by `ι`

The class `FinVec ι K X` guarantees that any element `x : X` can be writtens as:
```
∑ i, proj i x • basis i
```
-/
class Basis (ι : outParam $ Type v) (K : outParam $ Type w) (X : Type u)  where
  basis (i : ι) : X
  proj  (i : ι) (x : X) : K

/-- Dual basis of the space `X` over the field `K` indexed by `ι`

The class `FinVec ι K X` guarantees that any element `x : X` can be writtens as:
```
∑ i, proj i x • basis i
```
and that it is dual to the normal basis
```
⟪basis i, dualBasis j⟫[K] = if i=j then 1 else 0
```
-/
class DualBasis (ι  : outParam $ Type v) (K : outParam $ Type w) (X : Type u) where
  dualBasis (i : ι) : X
  dualProj  (i : ι) (x : X) : K

/-- This should somehow relate to raising and lowering indices but I forgot how.

TODO: add explanation why this is useful
-/
class BasisDuality (X : Type u) where
  toDual   (x : X) : X  -- transforms basis vectors to dual basis vectors
  fromDual (x : X) : X  -- transforma dual basis vectors to basis vectors

section Basis

  instance (K : Type _) [RCLike K] : Basis Unit K K :=
  {
    basis := λ _ => 1
    proj  := λ _ x => x
  }

  instance (K : Type _) [RCLike K] : DualBasis Unit K K :=
  {
    dualBasis := λ _ => 1
    dualProj  := λ _ x => x
  }

  instance (K : Type _) [RCLike K] : BasisDuality K :=
  {
    toDual := λ x => x
    fromDual  := λ x => x
  }

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

class OrthonormalBasis (ι K X : Type _) [Semiring K] [Basis ι K X] [Inner K X] : Prop where
  is_orthogonal : ∀ i j, i ≠ j → ⟪ⅇ[X] i, ⅇ j⟫[K] = 0
  is_orthonormal : ∀ i, ⟪ⅇ[X] i, ⅇ i⟫[K] = 1

/--
 -/
class FinVec (ι : outParam $ Type _) (K : Type _) (X : Type _) [outParam $ IndexType ι] [LawfulIndexType ι] [DecidableEq ι] [RCLike K] extends SemiHilbert K X, Basis ι K X, DualBasis ι K X, BasisDuality X where
  is_basis : ∀ x : X, x = ∑ i : ι, ℼ i x • ⅇ[X] i
  duality : ∀ i j, ⟪ⅇ[X] i, ⅇ'[X] j⟫[K] = if i=j then 1 else 0
  to_dual   : toDual   x = ∑ i,  ℼ i x • ⅇ'[X] i
  from_dual : fromDual x = ∑ i, ℼ' i x •  ⅇ[X] i


theorem basis_ext {ι K X} {_ : IndexType ι} [LawfulIndexType ι] [DecidableEq ι] [RCLike K] [FinVec ι K X] (x y : X)
  : (∀ i, ⟪x, ⅇ i⟫[K] = ⟪y, ⅇ i⟫[K]) → (x = y) := sorry_proof

theorem dualBasis_ext {ι K X} {_ : IndexType ι} [LawfulIndexType ι] [DecidableEq ι] [RCLike K] [FinVec ι K X] (x y : X)
  : (∀ i, ⟪x, ⅇ' i⟫[K] = ⟪y, ⅇ' i⟫[K]) → (x = y) := sorry_proof

theorem inner_proj_dualProj {ι K X} {_ : IndexType ι} [LawfulIndexType ι] [DecidableEq ι] [RCLike K] [FinVec ι K X] (x y : X)
  : ⟪x, y⟫[K] = ∑ i, ℼ i x * ℼ' i y :=
by
  calc
    ⟪x, y⟫[K] = ∑ i, ∑ j, ⟪(ℼ i x) • ⅇ[X] i, (ℼ' j y) • ⅇ' j⟫[K] := by sorry_proof -- rw[← (FinVec.is_basis x), ← (FinVec.is_basis y)]
         _ = ∑ i, ∑ j, (ℼ i x * ℼ' j y) * ⟪ⅇ[X] i, ⅇ' j⟫[K] := by sorry_proof -- use linearity of the sum
         _ = ∑ i, ∑ j, (ℼ i x * ℼ' j y) * if i=j then 1 else 0 := by simp [FinVec.duality]
         _ = ∑ i, ℼ i x * ℼ' i y := sorry_proof -- summing over [[i=j]]

variable {ι K X} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι] [RCLike K] [FinVec ι K X]


instance (priority:=low) : GetElem X ι K (fun _ _ => True) where
  getElem x i _ := ℼ i x

instance (priority:=low) : GetElem X ℕ K (fun _ i => i < IndexType.card ι) where
  getElem x i h := ℼ (IndexType.fromFin ⟨i,h⟩) x

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
by simp only [←inner_dualBasis_proj, inner_basis_dualBasis, eq_comm]; done

@[simp]
theorem proj_zero (i : ι)
  : ℼ i (0 : X) = 0 :=
by sorry_proof

@[simp]
theorem dualProj_dualBasis (i j : ι)
  : ℼ' i (ⅇ'[X] j) = if i=j then 1 else 0 :=
by simp only [←inner_basis_dualProj, inner_dualBasis_basis, eq_comm]; done

instance : FinVec Unit K K where
  is_basis := by simp[Basis.proj, Basis.basis]; sorry_proof
  duality := by simp[Basis.proj, Basis.basis, DualBasis.dualProj, DualBasis.dualBasis, Inner.inner]; done
  to_dual := by sorry_proof
  from_dual := by sorry_proof

instance : OrthonormalBasis Unit K K where
  is_orthogonal  := sorry_proof
  is_orthonormal := sorry_proof

-- @[infer_tc_goals_rl]
instance {ι κ K X Y}
    [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
    [IndexType κ] [LawfulIndexType κ] [DecidableEq κ]
    [RCLike K] [FinVec ι K X] [FinVec κ K Y] :
    FinVec (ι⊕κ) K (X×Y) where
  is_basis := sorry_proof
  duality := sorry_proof
  to_dual := sorry_proof
  from_dual := sorry_proof

instance
    [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
    [IndexType κ] [LawfulIndexType κ] [DecidableEq κ]
    [FinVec ι K X] [OrthonormalBasis ι K X]
    [FinVec κ K Y] [OrthonormalBasis κ K Y] :
    OrthonormalBasis (ι⊕κ) K (X×Y) where
  is_orthogonal  := by simp[Inner.inner, Basis.basis]; sorry_proof
  is_orthonormal := by simp[Inner.inner, Basis.basis]; sorry_proof


-- this might require `FinVec` instance, without it we probably do not know that `⟪0,x⟫ = 0`
instance [IndexType ι] [IndexType κ] [LawfulIndexType ι] [LawfulIndexType κ] [Zero X] [Basis κ K X] [OrthonormalBasis κ K X] : OrthonormalBasis (ι×κ) K (ι → X) where
  is_orthogonal  := by simp[Inner.inner, Basis.basis]; sorry_proof
  is_orthonormal := by simp[Inner.inner, Basis.basis]; sorry_proof


instance (priority:=high) {ι : Type} {K : Type v} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι] [RCLike K]
  : FinVec ι K (ι → K) where
  is_basis := sorry_proof
  duality := sorry_proof
  to_dual := sorry_proof
  from_dual := sorry_proof

instance {ι κ : Type} {K X : Type _} [IndexType ι] [IndexType κ] [LawfulIndexType ι] [LawfulIndexType κ] [DecidableEq ι] [DecidableEq κ] [RCLike K] [FinVec κ K X]
  : FinVec (ι×κ) K (ι → X) where
  is_basis := sorry_proof
  duality := sorry_proof
  to_dual := sorry_proof
  from_dual := sorry_proof
