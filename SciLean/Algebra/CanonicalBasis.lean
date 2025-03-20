import SciLean.Analysis.AdjointSpace.Basic
import SciLean.Analysis.AdjointSpace.Adjoint

namespace SciLean


-- class CanonicalBasis (I 𝕜 X : Type*) [RCLike 𝕜]
--       [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
--       [Fintype I] [DecidableEq I]
--   where
--   /-- `ⅇ[i]` is `i`-th basis vector of a vector space

--   Can be also written a `ⅇ[𝕜,X,i]` or `ⅇ[X,i]` to specify the vector space `X` and base field `𝕜`

--   To project a vector on this basis vector use `ℼ[i]` which notation for `proj i` -/
--   basis (i : I) : X
--   /-- `ⅇ'[i]` is `i`-th dual basis vector of a vector space

--   Can be also written a `ⅇ'[𝕜,X,i]` or `ⅇ'[X,i]` to specify the vector space `X` and base field `𝕜`

--   To project a vector on this basis vector use `ℼ'[i]` which notation for `dualProj i`

--   We have `dualBasis` because the basis `ⅇ[i]` is not necessarily orthonormal, but similar condition
--   holds between `ⅇ[i]` and `ⅇ'[j]`
--   ```
--     ⟪e[i], ⅇ'[j]⟫ = if i = j then 1 else 0
--   ```
--   -/
--   dualBasis (i : I) : X
--   /--
--   `ℼ[𝕜,i]` is the projection onto i-th basis vector.

--   Can be also written a `ℼ[𝕜,i]` to specify the base field `𝕜`
--   -/
--   proj  (i : I) (x : X) : 𝕜
--   /--
--   `ℼ[𝕜,i]` is the projection onto i-th dual basis vector.

--   Can be also written a `ℼ'[𝕜,i]` to specify the base field `𝕜`
--   -/
--   dualProj (i : I) (x : X) : 𝕜

--   basis_complete (x : X) : x = Finset.univ.sum (fun i : I => proj i x • basis i)

--   proj_basis (i j : I) : proj i (basis j) = if i = j then 1 else 0
--   dualProj_dualBasis (i j : I) : dualProj i (dualBasis j) = if i = j then 1 else 0
--   inner_basis_dualBasis (i j : I) : ⟪basis i, dualBasis j⟫[𝕜] = if i = j then 1 else 0



-- @[inherit_doc CanonicalBasis.basis]
-- macro:max "ⅇ[" k:term ", " X:term ", " i:term  "]" : term =>
--   `(CanonicalBasis.basis (𝕜:=$k) (X:=$X) $i)

-- @[inherit_doc CanonicalBasis.basis]
-- macro:max "ⅇ[" X:term ", " i:term  "]" : term =>
--   `(CanonicalBasis.basis (𝕜:=defaultScalar%) (X:=$X) $i)

-- @[inherit_doc CanonicalBasis.basis]
-- macro:max "ⅇ[" i:term  "]" : term =>
--   `(CanonicalBasis.basis (𝕜:=defaultScalar%) (X:=_) $i)


-- @[inherit_doc CanonicalBasis.dualBasis]
-- macro:max "ⅇ'[" k:term ", " X:term ", " i:term  "]" : term =>
--   `(CanonicalBasis.dualBasis (𝕜:=$k) (X:=$X) $i)

-- @[inherit_doc CanonicalBasis.dualBasis]
-- macro:max "ⅇ'[" X:term ", " i:term  "]" : term =>
--   `(CanonicalBasis.dualBasis (𝕜:=defaultScalar%) (X:=$X) $i)

-- @[inherit_doc CanonicalBasis.dualBasis]
-- macro:max "ⅇ'[" i:term  "]" : term =>
--   `(CanonicalBasis.dualBasis (𝕜:=defaultScalar%) (X:=_) $i)


-- @[inherit_doc CanonicalBasis.proj]
-- macro:max "ℼ[" k:term ", " i:term  "]" : term =>
--   `(CanonicalBasis.proj (𝕜:=$k) $i)

-- @[inherit_doc CanonicalBasis.proj]
-- macro:max "ℼ[" i:term  "]" : term =>
--   `(CanonicalBasis.proj (𝕜:=defaultScalar%) $i)


-- @[inherit_doc CanonicalBasis.proj]
-- macro:max "ℼ'[" k:term ", " i:term  "]" : term =>
--   `(CanonicalBasis.proj (𝕜:=$k) $i)

-- @[inherit_doc CanonicalBasis.proj]
-- macro:max "ℼ'[" i:term  "]" : term =>
--   `(CanonicalBasis.proj (𝕜:=defaultScalar%) $i)
