import SciLean.Data.DataArray.DataArray
import SciLean.Data.ArrayOperations.Algebra

namespace SciLean

/-- Type `X` is equivalent to `K^[I]`.

This class us useful for uncurrying arrays. For example derive equivalence
`K^[k]^[n]^[m] ≃ K^[m,n,k]` or `K^[k]^[n]^[m] ≃ K^[k]^[n,m]`

This class is often used in conjunction with `GetElem` or `DefaultIndex` to derive `K` or `I` as `outParam`. -/
class DataArrayEquiv (X : Type*) (I : Type*) (K : Type*)
    {n : outParam ℕ} [IdxType I n] [PlainDataType K] where
  equiv : X ≃ K^[I]  -- compiler can't see through Equiv!!!
  -- maybe require that `X` can be indexed by `I` and get `K` and the indexing commutes with this equivalence
  -- but that is a problem because we want to use this class to implement the index access

/-- `dataArrayEquiv K` is an equivalence between type `X` and `K^[I]` for appropriate `I`.
It is an abbreviation for `DataArrayEquiv.equiv (K:=K)`.

Often used with as `dataArrayEquiv Float` or `dataArrayEquiv ComplexFloat`. -/
@[inline]
abbrev dataArrayEquiv {X : Type*} (I K : Type*)
    {n} [IdxType I n] [PlainDataType K] [DataArrayEquiv X I K] :
    X ≃ K^[I] := DataArrayEquiv.equiv

-- base case
instance {I n} [IdxType I n] {K} [PlainDataType K] :
  DataArrayEquiv (K^[I]) I K where
  equiv := {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := by intro; simp
    right_inv := by intro; simp
  }

-- inductive
instance {I J X K : Type*}
    {nI} [IdxType I nI] {nJ} [IdxType J nJ] [PlainDataType K]
    [PlainDataType X] [DataArrayEquiv X J K] :
    DataArrayEquiv (X^[I]) (I×J) K where
  equiv := {
      toFun  x := ⟨⟨x.1.1, sorry_proof⟩, sorry_proof⟩
      invFun x := ⟨⟨x.1.1, sorry_proof⟩, sorry_proof⟩
      right_inv := sorry_proof
      left_inv := sorry_proof
    }


----------------------------------------------------------------------------------------------------
-- Default DataArrayEquiv for type `X` -------------------------------------------------------------
----------------------------------------------------------------------------------------------------

/-- Same as `DataArrayEquiv` but `I` and `K` are inferred based on `X`.

For example for `X = Float^[k]^[n]^[m]` this class inferes `I = Fin m × Fin n × Fin k` and `K = Float`.
-/
class DefaultDataArrayEquiv (X : Type*) (I K : outParam Type*) {n : outParam ℕ} [IdxType I n] [PlainDataType K]
  extends DataArrayEquiv X I K where

instance {R K I : Type*} {n} [IdxType I n] [Scalar R K] [PlainDataType K] :
    DefaultDataArrayEquiv (K^[I]) I K where

instance {K I : Type*} [PlainDataType K] {nI} [IdxType I nI] {nJ} [IdxType J nJ] [PlainDataType X]
    [DefaultDataArrayEquiv X J K] :
    DefaultDataArrayEquiv (X^[I]) (I×J) K where

@[inline]
abbrev toRn {X I K : Type*} {nI} [IdxType I nI] [PlainDataType K] [DefaultDataArrayEquiv X I K]
  (x : X) : K^[I] := (dataArrayEquiv I K).toFun x

@[inline]
abbrev fromRn {X I K : Type*} {nI} [IdxType I nI] [PlainDataType K] [DefaultDataArrayEquiv X I K]
  (x : K^[I]) : X := (dataArrayEquiv I K).invFun x


----------------------------------------------------------------------------------------------------
-- Get Element -------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

/-- Uncurry element access `x[i][j]` for `x : X^[I]` where `X` can be element accessed with `j : J` -/
instance {I J} {nI} [IdxType I nI] {nJ} [IdxType J nJ]
    {K} [PlainDataType K]
    {X} [PlainDataType X] [DataArrayEquiv X J K] [GetElem X J K (fun _ _ => True)] :
    GetElem (X^[I]) (I×J) K (fun _ _ => True) where
  getElem xs ij _ :=
    let scalarArray := (dataArrayEquiv (I×J) K).toFun xs
    scalarArray[ij]

/-- `x[i,j] = x[i][j]` for `x : X^[I]` -/
instance {I J} {nI} [IdxType I nI] {nJ} [IdxType J nJ]
    {K} [PlainDataType K]
    {X} [PlainDataType X] [DataArrayEquiv X J K] [GetElem X J K (fun _ _ => True)] :
    IsGetElemCurry (X^[I]) I J where
  getElem_curry := by
    apply (Equiv.forall_congr_left (dataArrayEquiv (K:=K) (X:=X^[I]) (I:=(I×J))) (p:=fun x => ∀ ij, x[ij] = _)).2
    intro x ij
    -- not sure if this is provable, we need
    --   `∀ j, x[j] = ((dataArrayEquiv K).symm x)[j]`
    -- but I don't think anything quarantees this right now
    sorry_proof

instance {I J} {nI} [IdxType I nI] {nJ} [IdxType J nJ]
    {K} [PlainDataType K]
    {X} [PlainDataType X] [DataArrayEquiv X J K] [GetElem X J K (fun _ _ => True)] :
    InjectiveGetElem (X^[I]) (I×J) where
  getElem_injective := by
    -- this should be an easy proof if we use that `I×J → K ≃ I → J → K`
    -- and that `fun x i => x[i]` and `∀ i, fun x j => x[i][j]` are injective
    sorry_proof


----------------------------------------------------------------------------------------------------
-- Set Element -------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

instance {I J} {nI} [IdxType I nI] {nJ} [IdxType J nJ]
    {K} [PlainDataType K]
    {X} [PlainDataType X] [DataArrayEquiv X J K] [GetElem X J K (fun _ _ => True)] :
    SetElem (X^[I]) (I×J) K (fun _ _ => True) where
  setElem xs ij v _ :=
    let scalarArray := dataArrayEquiv (I×J) K xs
    (dataArrayEquiv _ _).symm (setElem scalarArray ij v .intro)
  setElem_valid := by simp

instance {I J} {nI} [IdxType I nI] {nJ} [IdxType J nJ]
    {K} [PlainDataType K]
    {X} [PlainDataType X] [DataArrayEquiv X J K] [GetElem X J K (fun _ _ => True)] :
    LawfulSetElem (X^[I]) (I×J) where
  getElem_setElem_eq := sorry_proof
  getElem_setElem_neq := sorry_proof


----------------------------------------------------------------------------------------------------
-- OfFn --------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

instance {I J} {nI} [IdxType I nI] {nJ} [IdxType J nJ] [IdxType.Fold'.{_,0} I] [IdxType.Fold'.{_,0} J]
    {K} [PlainDataType K]
    {X} [PlainDataType X] [DataArrayEquiv X J K] [GetElem X J K (fun _ _ => True)] :
    OfFn (X^[I]) (I×J) K where
  ofFn f := (dataArrayEquiv _ _).symm (⊞ ij => f ij)

instance {I J} {nI} [IdxType I nI] {nJ} [IdxType J nJ] [IdxType.Fold'.{_,0} I] [IdxType.Fold'.{_,0} J]
    {K} [PlainDataType K]
    {X} [PlainDataType X] [DataArrayEquiv X J K] [GetElem X J K (fun _ _ => True)] :
    LawfulOfFn (X^[I]) (I×J) where
  getElem_ofFn := sorry_proof
