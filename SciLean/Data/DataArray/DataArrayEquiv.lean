import SciLean.Data.DataArray.DataArray
import SciLean.Data.ArrayOperations.Algebra

namespace SciLean

open Function


/-- Type `X` is equivalent to `K^[I]`.

This class us useful for uncurrying arrays. For example derive equivalence
`K^[k]^[n]^[m] ≃ K^[m,n,k]` or `K^[k]^[n]^[m] ≃ K^[k]^[n,m]`

This class is often used in conjunction with `GetElem` or `DefaultIndex` to derive `K` or `I` as `outParam`. -/
class DataArrayEquiv (X : Type*) (I : Type*) (K : outParam Type*)
    {n : outParam ℕ} [IndexType I n] [PlainDataType K] where
  toKn : X → K^[I]
  fromKn : K^[I] → X
  protected left_inv : LeftInverse fromKn toKn
  protected right_inv : RightInverse fromKn toKn

  -- maybe require that `X` can be indexed by `I` and get `K` and the indexing commutes with this equivalence
  -- but that is a problem because we want to use this class to implement the index access

  -- also probably require that `X` is `PlainDataType` and `toByteArray` commutes with `toKn`


/-- `HasRnEquiv X n R` says that `X` is canonically isomorphic to `R^[n]`

This provides class provides:
  - `toRn : X → R^[n]`
  - `fromRn : R^[n] → X`

This class is supposed to be zero cost at runtime or close to zero.
-/
class HasRnEquiv (X : Type*) (I R : outParam Type*) {nI : outParam ℕ}
    [RealScalar R] [PlainDataType R] [IndexType I nI]
  extends
    DataArrayEquiv X I R
  where


@[reducible, inline, macro_inline]
def toKn {X : Type*} (I K : Type*) {nI} [IndexType I nI] [PlainDataType K] [DataArrayEquiv X I K]
  (x : X) : K^[I] := DataArrayEquiv.toKn x

@[reducible, inline, macro_inline]
def fromKn (X : Type*) {I K : Type*} {nI} [IndexType I nI] [PlainDataType K] [DataArrayEquiv X I K]
  (x : K^[I]) : X := DataArrayEquiv.fromKn x

/--
Converts `X` to `R^[I]`

Similar to `toKn` but can infere `R` and `I` automatically.
-/
@[macro_inline]
def toRn {X I R : Type*} [RealScalar R] [PlainDataType R] {nI} [IndexType I nI] [HasRnEquiv X I R]
  (x : X) : R^[I] := DataArrayEquiv.toKn x

/--
Converts `R^[I]` to `X`

Similar to `fromKn` can infere `R` and `I` automatically.
-/
@[macro_inline]
def fromRn {X I R : Type*} [RealScalar R] [PlainDataType R] {nI} [IndexType I nI] [HasRnEquiv X I R]
  (x : R^[I]) : X := DataArrayEquiv.fromKn x


namespace DataArrayN
----------------------------------------------------------------------------------------------------
-- Basic Instances ---------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- inductive
instance instDataArrayEquivInductive
    {I J X K : Type*}
    {nI} [IndexType I nI] {nJ} [IndexType J nJ] [PlainDataType K]
    [PlainDataType X] [DataArrayEquiv X J K] :
    DataArrayEquiv (X^[I]) (I×J) K where
  toKn  x := cast sorry_proof x -- this is slow ⟨⟨x.1.1, sorry_proof⟩, sorry_proof⟩
  fromKn x := cast sorry_proof x -- this is slow ⟨⟨x.1.1, sorry_proof⟩, sorry_proof⟩
  right_inv := sorry_proof
  left_inv := sorry_proof


-- base case
instance instDataArrayEquivBase
    {I n} [IndexType I n] {K} [PlainDataType K] :
    DataArrayEquiv (K^[I]) I K where
  toKn := fun x => x
  fromKn := fun x => x
  left_inv := by intro; simp
  right_inv := by intro; simp


-- self
instance instDataArrayEquivSelf
    {K} [PlainDataType K] :
    DataArrayEquiv K Unit K where
  toKn := fun x => (⊞ (_ : Unit) => x : K^[Unit])
  fromKn := fun x => x[()]
  left_inv := by intro; simp
  right_inv := by intro; simp; sorry_proof



----------------------------------------------------------------------------------------------------
-- Index Get/Set Currying and Uncurrying -----------------------------------------------------------
----------------------------------------------------------------------------------------------------

----------------------------------------------------------------------------------------------------
-- Get Element -------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

/-- Uncurry element access `x[i][j]` for `x : X^[I]` where `X` can be element accessed with `j : J` -/
instance instGetElemUncurry
    {I J} {nI} [IndexType I nI] {nJ} [IndexType J nJ]
    {K} [PlainDataType K]
    {X} [PlainDataType X] [DataArrayEquiv X J K] :
    GetElem (X^[I]) (I×J) K (fun _ _ => True) where
  getElem xs ij _ :=
    let scalarArray := toKn (I×J) K xs
    scalarArray[ij]

instance {I J} {nI} [IndexType I nI] {nJ} [IndexType J nJ]
    {K} [PlainDataType K]
    {X} [PlainDataType X] [DefaultIndexOfRank X r J] [DataArrayEquiv X J K] :
    DefaultIndexOfRank (X^[I]) (r+1) (I×J) where


/-- `x[i,j] = x[i][j]` for `x : X^[I]` -/
instance instIsGetElemCurry
    {I J} {nI} [IndexType I nI] {nJ} [IndexType J nJ]
    {K} [PlainDataType K]
    {X} [PlainDataType X] [DataArrayEquiv X J K] [GetElem' X J K] :
    IsGetElemCurry (X^[I]) I J where
  getElem_curry := by
    -- I don't think it is provable with the current set of assumptions
    -- something extra is likely necessary
    sorry_proof

instance instInjectiveGetElemUncurry
    {I J} {nI} [IndexType I nI] {nJ} [IndexType J nJ]
    {K} [PlainDataType K]
    {X} [PlainDataType X] [DataArrayEquiv X J K] :
    InjectiveGetElem (X^[I]) (I×J) where
  getElem_injective := by
    -- this should be an easy proof if we use that `I×J → K ≃ I → J → K`
    -- and that `fun x i => x[i]` and `∀ i, fun x j => x[i][j]` are injective
    sorry_proof


----------------------------------------------------------------------------------------------------
-- Set Element -------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

instance instSetElemUncurry
    {I J} {nI} [IndexType I nI] {nJ} [IndexType J nJ]
    {K} [PlainDataType K]
    {X} [PlainDataType X] [DataArrayEquiv X J K] :
    SetElem (X^[I]) (I×J) K (fun _ _ => True) where
  setElem xs ij v _ :=
    let scalarArray := toKn (I×J) K xs
    fromKn _ (setElem scalarArray ij v .intro)
  setElem_valid := by simp

instance instLawfulSetElemUncurry
    {I J} {nI} [IndexType I nI] {nJ} [IndexType J nJ]
    {K} [PlainDataType K]
    {X} [PlainDataType X] [DataArrayEquiv X J K] [GetElem X J K (fun _ _ => True)] :
    LawfulSetElem (X^[I]) (I×J) where
  getElem_setElem_eq := sorry_proof
  getElem_setElem_neq := sorry_proof


----------------------------------------------------------------------------------------------------
-- OfFn --------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

instance instOfFnUncurry
    {I J} {nI} [IndexType I nI] {nJ} [IndexType J nJ] [Fold.{_,0} I] [Fold.{_,0} J]
    {K} [PlainDataType K]
    {X} [PlainDataType X] [DataArrayEquiv X J K] [GetElem X J K (fun _ _ => True)] :
    OfFn (X^[I]) (I×J) K where
  ofFn f := fromKn _ (⊞ ij => f ij)

instance instLawfulOfFnUncurry
    {I J} {nI} [IndexType I nI] {nJ} [IndexType J nJ] [Fold.{_,0} I] [Fold.{_,0} J]
    {K} [PlainDataType K]
    {X} [PlainDataType X] [DataArrayEquiv X J K] [GetElem X J K (fun _ _ => True)] :
    LawfulOfFn (X^[I]) (I×J) where
  getElem_ofFn := sorry_proof
