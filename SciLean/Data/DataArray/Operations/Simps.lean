import SciLean.Data.DataArray.Operations
import SciLean.Data.ArrayType.Properties

/-! Basic simp theorems about matrix operations -/


namespace SciLean

section Missing

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
  {I : Type} [IndexType I]
  {J : Type} [IndexType J]
  {K : Type} [IndexType K]
  {L : Type} [IndexType L]
  {R : Type} [RealScalar R] [PlainDataType R]

theorem vecmul_def (A : R^[I,J]) (x : R^[J]) : A * x = ⊞ i => ∑ j, A[i,j] * x[j] := rfl

theorem matmul_def (A : R^[I,J]) (B : R^[J,K]) : A * B = ⊞ i k => ∑ j, A[i,j] * B[j,k] := rfl

section

variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]

set_default_scalar R

@[simp, simp_core]
theorem identity_vecmul (x : R^[I]) : (𝐈 I) * x = x := by
  ext; simp[identity,vecmul_def,sum_ite']

@[simp, simp_core]
theorem identity_vecmul_smul (x : R^[I]) (c : R) :
    (c • (𝐈 I)) * x = c • x := by
  ext; simp[identity,vecmul_def,sum_ite']

@[simp, simp_core]
theorem identity_matmul (A : R^[I,I]) : (𝐈 I) * A = A := by
  ext i; cases i; simp[identity,matmul_def,sum_ite']

@[simp, simp_core]
theorem identity_matmul_smul (A : R^[I,I]) (c : R) :
    (c • (𝐈 I)) * A = c • A := by
  ext i; cases i; simp[identity,matmul_def,sum_ite']

@[simp, simp_core]
theorem matmul_identity (A : R^[I,I]) : A * (𝐈 I) = A := by
  ext i; cases i; simp[identity,matmul_def,sum_ite]

@[simp, simp_core]
theorem matmul_smul_identity (A : R^[I,I]) (c : R) :
    A * (c • (𝐈 I)) = c • A := by
  ext i; cases i; simp[identity,matmul_def,sum_ite,mul_comm]

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

@[neg_push]
theorem vecmul_neg_push (A : R^[I,J]) (x : R^[J]) :
    -(A*x) = A*(-x) := by
  ext i
  simp[vecmul_def]
  sorry_proof

@[neg_pull]
theorem vecmul_neg_pull_left (A : R^[I,J]) (x : R^[J]) :
    -A*x = -(A*x) := by
  ext i
  simp only [neg_pull,vecmul_def]

  sorry_proof

@[neg_push]
theorem neg_fun_push [Neg X] (f : α → X) :
    - f = fun x => - (f x) := by rfl

@[neg_pull]
theorem vecmul_neg_pull_right (A : R^[I,J]) (x : R^[J]) :
    A*-x = -(A*x) := by
  ext i
  simp only [neg_pull,vecmul_def]
  conv => rhs; simp only [neg_push]
  sorry_proof



theorem vecmul_normalize (A : R^[I,J]) (B : R^[J,K]) :
    A.matmul B = A * B := rfl

theorem matmul_normalize (A : R^[I,J]) (B : R^[J,K]) :
    A.matmul B = A * B := rfl


section

variable [DecidableEq I]

theorem inv_normalize (A : R^[I,I]) :
    A.inv = A⁻¹ := rfl

@[simp, simp_core]
theorem tranpose_inv_eq_inv_transpose (A : R^[I,I]) :
    A⁻¹ᵀ = A⁻ᵀ := sorry_proof

@[simp, simp_core]
theorem inv_inv (A : R^[I,I]) (hA : A.Invertible) : (A⁻¹)⁻¹ = A := sorry_proof

@[simp, simp_core]
theorem det_inv_eq_inv_det (A : R^[I,I]) :
    (A⁻¹).det = (A.det)⁻¹ := sorry_proof


end

section CrossProduct

@[simp, simp_core]
theorem cossmatrix_antisymmpart (x : R^[3]) :
  x.crossmatrix.antisymmpart = x := by sorry_proof

end CrossProduct
