import SciLean.Data.VectorType.Base


namespace SciLean

namespace VectorTypeScalar

-- open ComplexConjugate in
scoped instance {R K} [RealScalar R] [Scalar R K] : VectorType.Base K Unit K := {
  toVec := fun x _ => x
  zero := 0
  zero_spec := by funext i; simp
  scal := fun k x => k * x
  scal_spec := by intros; funext i; simp
  sum := fun x => x
  sum_spec := by simp
  asum := fun x => Scalar.abs x
  asum_spec := by intros; simp; sorry_proof
  nrm2 := fun x => Scalar.abs x
  nrm2_spec := by intros; simp; sorry_proof
  iamax := fun x => ()
  iamax_spec := by intros; simp; sorry_proof
  imaxRe := fun x _ => ()
  imaxRe_spec := by intros; simp
  iminRe := fun x _ => ()
  iminRe_spec := by intros; simp
  dot := fun x y => starRingEnd _ x * y
  dot_spec := by simp
  conj := fun x => starRingEnd _ x
  conj_spec := by intros; rfl
  axpy := fun a x y => a * x + y
  axpy_spec := by intros; funext i; simp
  axpby := fun a x b y => a * x + b * y
  axpby_spec := by intros; funext i; simp
  mul := fun x y => x * y
  mul_spec := by intros; funext i; simp
}


example {R K} [RealScalar R] [Scalar R K] : VectorType.Base K Unit K := by infer_instance

open VectorType in
local instance {R K} [RealScalar R] [Scalar R K] : VectorType.Dense (n:=Unit) (K:=K) K where
  fromVec := fun f => f ()
  right_inv := by intro x; simp[VectorType.toVec]
  set := fun x i v => v
  set_spec := by intros; simp[toVec]
  const := fun k => k
  const_spec := by simp[toVec]
  scalAdd := fun a b x => a * x + b
  scalAdd_spec := by simp[toVec]
  div := fun x y => x / y
  div_spec := by intros; funext i; simp[toVec]
  inv := fun x => x⁻¹
  inv_spec := by intros; funext i; simp[toVec]
  exp := fun x => Scalar.exp x
  exp_spec := by intros; funext i; simp[toVec]

end VectorTypeScalar
