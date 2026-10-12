module

public import SciLean.Analysis.AdjointSpace.CanonicalBasis
public import SciLean.Data.DataArray.Algebra
public import SciLean.Data.ArrayOperations.Operations.GetElem

@[expose] public section


namespace SciLean


variable {R : Type*} [RealScalar R] [PlainDataType R]
  [BLAS (DataArray R) R R] [LawfulBLAS (DataArray R) R R]
  {I nI} [IndexType I nI]

instance (priority:=high) : CanonicalBasis I R (R^[I]) where
  basis i := setElem (0 : R^[I]) i 1 .intro
  dualBasis i := setElem (0 : R^[I]) i 1 .intro
  proj i x := x[i]
  dualProj i x := x[i]
  basis_complete := by
    classical
    intro x; ext j
    rw [getElem_finset_sum]
    simp
  proj_basis := by classical intro i j; by_cases i = j <;> aesop
  dualProj_dualBasis := by classical intro i j; by_cases i = j <;> aesop
  inner_basis_dualBasis := by
    classical
    intro i j
    rw [IsInnerGetElem.inner_eq_sum_getElem (𝕜:=R) (X:=R^[I]) (I:=I) (Y:=R) (n:=nI)]
    simp [eq_comm (a:=i) (b:=j)]
  proj_linear := by intro i; fun_prop
  dualProj_linear := by intro i; fun_prop


-- instance
--     {X : Type*} {nI} [IndexType I nI] [PlainDataType K]
--     [DefaultDataArrayEquiv X I K] [GetElem X I K (fun _ _ => True)]
--     [RealScalar R] [Scalar R K]
--     [BLAS (DataArray K) R K] [LawfulBLAS (DataArray K) R K] :
--     CanonicalBasis I K X where
--   basis i := setElem (0 : R^[I]) i 1 .intro
--   dualBasis i := setElem (0 : R^[I]) i 1 .intro
--   proj i x := x[i]
--   dualProj i x := x[i]
--   basis_complete := by intros; ext i; simp[sum_pull]; sorry_proof
--   proj_basis := by classical intro i j; by_cases i = j <;> aesop
--   dualProj_dualBasis :=  by classical intro i j; by_cases i = j <;> aesop
--   inner_basis_dualBasis := sorry_proof
--   proj_linear := sorry_proof
--   dualProj_linear := sorry_proof

-- /-- Has canonical equivalence with `ℝⁿ`. -/
-- class HasRnEquiv (X : Type*) (n : outParam ℕ) (R : outParam Type*)
--    [RealScalar R] [PlainDataType R]
--    where
--    equiv : X ≃ R^[n]

-- #check Add.ofRnEquiv

-- class IsGetSetBasis (I 𝕜 X : Type*) [GetElem' X I 𝕜] [SetElem' X I 𝕜]
--   [RCLike 𝕜] [NormedAddCommGroup X] [AdjointSpace 𝕜 X] [CanonicalBasis I 𝕜 X]


end SciLean
