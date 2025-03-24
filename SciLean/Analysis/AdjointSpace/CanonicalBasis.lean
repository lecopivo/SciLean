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
  basis_complete := sorry_proof
  proj_basis := sorry_proof
  dualProj_dualBasis := sorry_proof
  inner_basis_dualBasis := sorry_proof
  proj_linear := sorry_proof
  dualProj_linear := sorry_proof


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

  basis_complete := sorry_proof
  proj_basis := sorry_proof
  dualProj_dualBasis := sorry_proof
  inner_basis_dualBasis := sorry_proof
  proj_linear := sorry_proof
  dualProj_linear := sorry_proof

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

  basis_complete := sorry_proof
  proj_basis := sorry_proof
  dualProj_dualBasis := sorry_proof
  inner_basis_dualBasis := sorry_proof
  proj_linear := sorry_proof
  dualProj_linear := sorry_proof


def CanonicalBasis.ofEquiv
    {J : Type*} (I : Type*) {Y : Type*} (X : Type*)
    {𝕜 : Type*} [RCLike 𝕜]
    [Fintype I] [Fintype J]
    [NormedAddCommGroup X] [AdjointSpace 𝕜 X] [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
    [CanonicalBasis I 𝕜 X]
    (f : I ≃ J) (g : X ≃ Y) : CanonicalBasis J 𝕜 Y where
  basis j := g ⅇ[𝕜,X, f.symm j]
  dualBasis j := g ⅇ'[𝕜,X, f.symm j]
  proj j y := ℼ[𝕜,f.symm j] (g.symm y)
  dualProj j y := ℼ'[𝕜,f.symm j] (g.symm y)

  basis_complete := sorry_proof
  proj_basis := sorry_proof
  dualProj_dualBasis := sorry_proof
  inner_basis_dualBasis := sorry_proof
  proj_linear := sorry_proof
  dualProj_linear := sorry_proof

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
  (∀ (i : I), ⟪x, ⅇ[i]⟫ = ⟪y, ⅇ[i]⟫) → (x = y) := sorry_proof

variable (I 𝕜) in
theorem dualBasis_ext {x y : X} :
  (∀ (i : I), ⟪x, ⅇ'[i]⟫ = ⟪y, ⅇ'[i]⟫) → (x = y) := sorry_proof

theorem inner_eq_sum_proj_dualProj (x y : X)
  : ⟪x, y⟫ = ∑ (i : I), ℼ[i] x * ℼ'[i] y :=
by
  classical
  calc
    ⟪x, y⟫ = ∑ i, ∑ j, ⟪(ℼ[i] x) • ⅇ[X,i], (ℼ'[j] y) • ⅇ'[j]⟫ := by sorry_proof
         _ = ∑ i, ∑ j, (ℼ[i] x * ℼ'[j] y) * ⟪ⅇ[X,i], ⅇ'[j]⟫ := by sorry_proof -- use linearity of the sum
         _ = ∑ i, ∑ j, (ℼ[i] x * ℼ'[j] y) * if i=j then 1 else 0 := by sorry_proof
         _ = ∑ i, ℼ[i] x * ℼ'[i] y := sorry_proof -- summing over [[i=j]]


@[simp, simp_core]
theorem inner_basis_dualBasis [DecidableEq I] (i j : I) :
    ⟪ⅇ[X,i], ⅇ'[j]⟫ = if i=j then 1 else 0 := by
  simp[CanonicalBasis.inner_basis_dualBasis]

@[simp, simp_core]
theorem inner_dualBasis_basis [DecidableEq I] (i j : I) :
    ⟪ⅇ'[X,i], ⅇ[j]⟫ = if i=j then 1 else 0 := by sorry_proof

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
  IsLinearMap 𝕜 (fun x : X => ℼ[i] x) := sorry_proof

@[fun_prop]
theorem CanonicalBasis.proj.arg_x.IsContinuousLinearMap_rule (i : I) :
  IsContinuousLinearMap 𝕜 (fun x : X => ℼ[i] x) := sorry_proof

#generate_linear_map_simps CanonicalBasis.proj.arg_x.IsLinearMap_rule


@[fun_prop]
theorem CanonicalBasis.dualProj.arg_x.IsLinearMap_rule (i : I) :
  IsLinearMap 𝕜 (fun x : X => ℼ'[i] x) := sorry_proof

@[fun_prop]
theorem CanonicalBasis.dualProj.arg_x.IsContinuousLinearMap_rule (i : I) :
  IsContinuousLinearMap 𝕜 (fun x : X => ℼ'[i] x) := sorry_proof

#generate_linear_map_simps CanonicalBasis.dualProj.arg_x.IsLinearMap_rule


-- TODO: remove `IndexType`
@[simp]
theorem inner_dualBasis_right_eq_proj (i : I) (x : X) :
    ⟪x, ⅇ'[i]⟫ = ℼ[i] x := by
  classical
  calc
    ⟪x, ⅇ'[i]⟫ = ⟪∑ j, ℼ[j] x • ⅇ[X,j], ⅇ'[X,i]⟫ := by sorry_proof
            _ = ∑ j, ℼ[j] x * if j=i then 1 else 0 := by sorry_proof
            _ = ℼ[i] x := by sorry_proof

@[simp]
theorem inner_dualBasis_left_eq_proj (i : I) (x : X) :
    ⟪ⅇ'[i], x⟫ = ℼ[i] x := by sorry_proof

@[simp]
theorem inner_basis_right_eq_dualProj (i : I) (x : X) :
    ⟪x, ⅇ[i]⟫ = ℼ'[i] x := by sorry_proof

@[simp]
theorem inner_basis_left_eq_dualProj (i : I) (x : X) :
    ⟪ⅇ[i], x⟫ = ℼ'[i] x := by sorry_proof
