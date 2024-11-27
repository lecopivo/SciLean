import SciLean.Data.DataArray.Operations

/-! Basic simp theorems about matrix operations -/


namespace SciLean

section Missing


theorem sum_over_prod' {R} [AddCommMonoid R] {I J : Type*} [IndexType I] [IndexType J]
    {f : I → J → R} : ∑ i j, f i j = ∑ (i : I×J), f i.1 i.2  := sorry

theorem sum_over_prod {R} [AddCommMonoid R] {I J : Type*} [IndexType I] [IndexType J]
    {f : I×J → R} : ∑ i, f i = ∑ i j, f (i,j)  := sorry

@[rsimp]
theorem sum_ite {R} [AddCommMonoid R] {I : Type*} [IndexType I] [DecidableEq I]
    {f : I → R} (j : I) : (∑ i, if i = j then f i else 0) = f j  := sorry

@[rsimp]
theorem sum_ite' {R} [AddCommMonoid R] {I : Type*} [IndexType I] [DecidableEq I]
    {f : I → R} (j : I) : (∑ i, if j = i then f i else 0) = f j  := sorry

theorem sum_swap {R} [AddCommMonoid R] {I J : Type*} [IndexType I] [IndexType J]
    {f : I → J → R} : ∑ i j, f i j = ∑ j i, f i j  := sorry

@[simp,simp_core]
theorem uncurry_appply2 (f : α → β → γ) (x : α) (y : β) :
    (↿f) (x,y) = f x y := rfl

-- ideally this should be only `rsimp` theorems at it has a binder but it is too useful and
-- we do not run `rsimp` by default
@[simp, simp_core]
theorem sum_const_scalar {R} [RCLike R] {I : Type*} [IndexType I] (c : R) :
    ∑ (i : I), c = (Size.size I : R) • c := sorry

end Missing

namespace DataArrayN

variable
  {I : Type*} [IndexType I]
  {J : Type*} [IndexType J]
  {K : Type*} [IndexType K]
  {L : Type*} [IndexType L]
  {R : Type*} [RealScalar R] [PlainDataType R]

theorem vecmul_def (A : R^[I,J]) (x : R^[J]) : A * x = ⊞ i => ∑ j, A[i,j] * x[j] := rfl

theorem matmul_def (A : R^[I,J]) (B : R^[J,K]) : A * B = ⊞ i k => ∑ j, A[i,j] * B[j,k] := rfl

section

variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]

@[simp, simp_core]
theorem identity_vecmul (x : R^[I]) : Matrix.identity (R:=R) (I:=I) * x = x := by
  ext; simp[Matrix.identity,vecmul_def,sum_ite']

@[simp, simp_core]
theorem identity_vecmul_smul (x : R^[I]) (c : R) :
    (c • Matrix.identity (R:=R) (I:=I)) * x = c • x := by
  ext; simp[Matrix.identity,vecmul_def,sum_ite']

@[simp, simp_core]
theorem identity_matmul (A : R^[I,I]) : Matrix.identity (R:=R) (I:=I) * A = A := by
  ext i; cases i; simp[Matrix.identity,matmul_def,sum_ite']

@[simp, simp_core]
theorem identity_matmul_smul (A : R^[I,I]) (c : R) :
    (c • Matrix.identity (R:=R) (I:=I)) * A = c • A := by
  ext i; cases i; simp[Matrix.identity,matmul_def,sum_ite']

@[simp, simp_core]
theorem matmul_identity (A : R^[I,I]) : A * Matrix.identity (R:=R) (I:=I) = A := by
  ext i; cases i; simp[Matrix.identity,matmul_def,sum_ite]

@[simp, simp_core]
theorem matmul_smul_identity (A : R^[I,I]) (c : R) :
    A * (c • Matrix.identity (R:=R) (I:=I)) = c • A := by
  ext i; cases i; simp[Matrix.identity,matmul_def,sum_ite,mul_comm]

end

@[simp, simp_core]
theorem zero_vecmul (b : R^[J]) : (0 : R^[I,J]) * b = 0 := by
  ext i; simp[vecmul_def]

@[simp, simp_core]
theorem vecmul_zero (A : R^[I,J]) : A * (0 : R^[J]) = 0 := by
  ext i; simp[vecmul_def]

@[simp, simp_core]
theorem zero_matmul (B : R^[J,K]) : (0 : R^[I,J]) * B = 0 := by
  ext i; cases i; simp[matmul_def]

@[simp, simp_core]
theorem matmul_zero (A : R^[I,J]) : A * (0 : R^[J,K]) = 0 := by
  ext i; cases i; simp[matmul_def]

theorem vecmul_assoc (A : R^[I,J]) (B : R^[J,K]) (x : R^[K]) :
    A * B * x = A * (B * x) := by
  ext i
  simp[vecmul_def,matmul_def,sum_pull,mul_assoc]
  rw[sum_swap]

theorem matmul_assoc (A : R^[I,J]) (B : R^[J,K]) (C : R^[K,L]) :
    A * B * C = A * (B * C) := by
  ext i; cases i
  simp[matmul_def,sum_pull,mul_assoc]
  rw[sum_swap]


@[neg_push]
theorem matmul_neg_push (A : R^[I,J]) (B : R^[J,K]) :
    -(A*B) = -A*B := by
  ext i; cases i;
  simp[matmul_def]
  sorry_proof

@[neg_pull]
theorem matmul_neg_pull_left (A : R^[I,J]) (B : R^[J,K]) :
    -A*B = -(A*B) := by
  simp only [neg_push]

@[neg_pull]
theorem matmul_neg_pull_right (A : R^[I,J]) (B : R^[J,K]) :
    A*-B = -(A*B) := by
  ext i; cases i;
  simp [neg_pull,matmul_def]
  sorry_proof

@[neg_push]
theorem vecmul_neg_push (A : R^[I,J]) (x : R^[J]) :
    -(A*x) = -A*x := by
  ext i
  simp[vecmul_def]
  sorry_proof

@[neg_pull]
theorem vecmul_neg_pull_left (A : R^[I,J]) (x : R^[J]) :
    -A*x = -(A*x) := by
  simp only [neg_push]

@[neg_pull]
theorem vecmul_neg_pull_right (A : R^[I,J]) (x : R^[J]) :
    A*-x = -(A*x) := by
  ext i
  simp [neg_pull,vecmul_def]
  sorry_proof


theorem vecmul_normalize (A : R^[I,J]) (B : R^[J,K]) :
    A.matmul B = A * B := rfl

theorem matmul_normalize (A : R^[I,J]) (B : R^[J,K]) :
    A.matmul B = A * B := rfl

theorem inv_normalize [DecidableEq I] (A : R^[I,I]) :
    A.inv = A⁻¹ := rfl

@[simp, simp_core]
theorem tranpose_inv_eq_inv_transpose [DecidableEq I] (A : R^[I,I]) :
    A⁻¹ᵀ = A⁻ᵀ := sorry_proof
