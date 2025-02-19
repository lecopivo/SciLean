import SciLean.Data.VectorType.Base


namespace SciLean

namespace VectorTypeScalar

-- open ComplexConjugate in
scoped instance {R K} [RealScalar R] [Scalar R K] : VectorType.Base K Unit K := {
  getElem x i _ := x
  zero := 0
  zero_spec := by intro i; simp
  scal := fun k x => k * x
  scal_spec := by intros _ i; simp
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
  axpy_spec := by intros;  simp
  axpby := fun a x b y => a * x + b * y
  axpby_spec := by intros; simp
  mul := fun x y => x * y
  mul_spec := by intros; simp
}


example {R K} [RealScalar R] [Scalar R K] : VectorType.Base K Unit K := by infer_instance

local instance {R K} [RealScalar R] [Scalar R K] : SetElem K n K (fun _ _ => True) where
  setElem := fun x i v _ => v
  setElem_valid := by simp

open VectorType in
local instance {R K} [RealScalar R] [Scalar R K] : VectorType.Dense (n:=Unit) (K:=K) K where
  getElem_setElem_eq := by intros; simp[getElem,setElem]
  getElem_setElem_neq := by intros; aesop
  fromVec := fun f => f ()
  right_inv := by intro x; simp[getElem,setElem]
  const := fun k => k
  const_spec := by simp[getElem]
  scalAdd := fun a b x => a * x + b
  scalAdd_spec := by simp[getElem]
  div := fun x y => x / y
  div_spec := by intros; simp[getElem]
  inv := fun x => x⁻¹
  inv_spec := by intros; simp[getElem]
  exp := fun x => Scalar.exp x
  exp_spec := by intros; simp[getElem]

end VectorTypeScalar
