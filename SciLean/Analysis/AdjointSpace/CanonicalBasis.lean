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

  basis_dualBasis (i j : I) : ⟪basis i, dualBasis j⟫[𝕜] = (if i = j then 1 else 0)
  proj_basis (i j : I) : proj i (basis j) = (if i = j then 1 else 0)
  dualProj_dualBasis (i j : I) : dualProj i (dualBasis j) = (if i = j then 1 else 0)

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
