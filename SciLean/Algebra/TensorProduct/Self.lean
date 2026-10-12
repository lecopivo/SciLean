module

public import SciLean.Algebra.TensorProduct.Basic
public import SciLean.Analysis.AdjointSpace.CanonicalBasis
public import SciLean.Data.DataArray.DataArray

@[expose] public section


namespace SciLean

/--
Class providing identity matrix of type `X ⊗ X`
 -/
class TensorProductSelf
    (R X : Type*) (XX : outParam Type*) [RCLike R]
    [NormedAddCommGroup X] [AdjointSpace R X]
    [AddCommGroup XX] [Module R XX]
    [TensorProductType R X X XX]
  where
    /-- Identit matrix `𝐈` -/
    identityMatrix : XX
    identityMatrix_spec (x : X) :
      matVecMulAdd (1:R) identityMatrix x 0 0 = x

    /-- `addIdentityMatrix a A = A + a•𝐈` - adds `a` multiple of identity to `A` -/
    addIdentityMatrix (a : R) (A : XX) : XX
    addIdentityMatrix_spec (a : R) (A : XX) :
      addIdentityMatrix a A = a • identityMatrix + A

export TensorProductSelf (identityMatrix addIdentityMatrix)

section Self

variable
    {R X XX : Type*} [RCLike R]
    [NormedAddCommGroup X] [AdjointSpace R X]
    [AddCommGroup XX] [Module R XX]
    [TensorProductType R X X XX]
    [ts : TensorProductSelf R X XX]

instance : TensorProductSelf R R R where
  identityMatrix := 1
  identityMatrix_spec := by intro x; simp [TensorProductType.matVecMulAdd]
  addIdentityMatrix r A := r + A
  addIdentityMatrix_spec := by simp


@[simp, simp_core]
theorem identityMatrix_scalar : identityMatrix R R = (1 :R) := by rfl

@[simp, simp_core]
theorem addIdentityMatrix_scalar (r A : R) : addIdentityMatrix R r A = r + A := by rfl

theorem addIdentityMatrix_def (a : R) (A : XX) :
  ts.addIdentityMatrix a A = A + a•ts.identityMatrix := by
  rw [ts.addIdentityMatrix_spec]; abel


@[simp, simp_core]
theorem matVecMulAdd_identityMatrix (a b : R) (x y : X) :
    matVecMulAdd a ts.identityMatrix x b y
    =
    a•x+b•y := by
  rw [matVecMulAdd_eq_smul_add, ts.identityMatrix_spec]

@[simp, simp_core]
theorem matVecMulAdd_addIdentityMatrix (a b c : R) (A : XX) (x y : X) :
    matVecMulAdd a (ts.addIdentityMatrix c A) x b y
    =
    matVecMulAdd a A x 1 ((a*c)•x + b•y) := by sorry_proof

@[simp, simp_core]
theorem vecMatMulAdd_identityMatrix (a b : R) (x y : X) :
    vecMatMulAdd a x ts.identityMatrix b y
    =
    a•x+b•y := by sorry_proof

@[simp, simp_core]
theorem vecMatMulAdd_addIdentityMatrix (a b c : R) (A : XX) (x y : X) :
    vecMatMulAdd a x (ts.addIdentityMatrix c A) b y
    =
    vecMatMulAdd a x A 1 ((a*c)•x + b•y) := by sorry_proof

@[simp, simp_core]
theorem addIdentityMatrix_zero (a : R) :
    ts.addIdentityMatrix a (0 : XX) = a•ts.identityMatrix := by
  simp[addIdentityMatrix_def]

end Self

----------------------------------------------------------------------------------------------------
-- Notation for Identity Matrix --------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

open Lean Meta Elab Term Qq in
/--
`𝐈[𝕜,X]` is identity matrix on `X` which is a vector space over field 𝕜

`𝐈[𝕜,n]` is identityt matrix on `𝕜^[n]` where `𝕜` is the default scalar
-/
elab (priority:=high) "𝐈[" k:term "," X:term "]" : term <= XX => do

  -- if `X` is natural number
  try
    let n ← elabTermAndSynthesize X q(Nat)
    let K ← elabTerm k none
    let I ← mkAppM ``Idx #[n]
    let X ← mkAppOptM ``DataArrayN #[K, none, I,none,none]
    let XX ← mkAppOptM ``DataArrayN #[K, none, (← mkAppM ``Prod #[I,I]), none,none]
    let id ← mkAppOptM ``identityMatrix #[K,X,XX,none,none,none,none,none,none,none]
    return id
  catch _ =>
    pure ()

  elabTerm (← `(identityMatrix $k $X)) XX --(cls.getArg! 2)

/--
`𝐈[X]` is the identity matrix for space `X`.

`𝐈[n]` is identityt matrix on `R^[n]` where `R` is the default scalar
 -/
macro "𝐈[" X:term "]" : term => `(𝐈[defaultScalar%, $X])

/-- `𝐈` is the identity Matrix  -/
macro "𝐈" : term => `(𝐈[defaultScalar%, _])

@[app_unexpander identityMatrix] meta def unexpandIdentityMatrix : Lean.PrettyPrinter.Unexpander
  | `($(_) $_ $_) => `(𝐈)
  | _ => throw ()



----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

/--
Class providing operations on diagonals of matrices of type `X ⊗ X`

Is there basis free version?
 -/
class TensorProductDiag
    (R X XX : Type*) [RCLike R]
    [NormedAddCommGroup X] [AdjointSpace R X]
    [AddCommGroup XX] [Module R XX]
    [tp : TensorProductType R X X XX]
    [Fintype I] [CanonicalBasis I R X]
  where

    /-- Turn vector `x` into diagonal matrix -/
    diagonal (x : X) : XX
    diagonal_spec : ∀ (x : X) ,
      (diagonal x)
      =
      -- ∑ i, (ℼ i x) • (ⅇ i) ⊗ (ⅇ i)
      Finset.univ.sum fun (i : I) =>
        (ℼ[R,i] x) • (tmulAdd (1:R) ⅇ[R,X,i] ⅇ'[R,X,i] 0)

    /-- Turn vector `x` into diagonal matrix -/
    diag (A : XX) : X
    diag_spec : ∀ (A : XX) (i : I) ,
      ℼ[R,i] (diag A)
      =
      -- ℼ[i] (A * ⅇ[i])
      ℼ[R,i] (tp.matVecMulAdd (1:R) A ⅇ[R,X,i] 0 0)

    addDiag (a : R) (x : X) (A : XX) : XX
    addDiag_spec (a : R) (x : X) (A : XX) :
      addDiag a x A
      =
      a • diagonal x + A
