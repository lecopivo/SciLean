import LeanBLAS.Vector.DenseVector

import SciLean.Data.IndexType
import SciLean.Data.VectorType.Base
import SciLean.Analysis.Scalar.FloatAsReal

namespace SciLean

open BLAS IndexType


structure FloatVector' (storage : DenseVector.Storage) (n : Type*) [IndexType n] where
  data : DenseVector FloatArray storage (size n) Float

abbrev FloatVector (n : Type*) [IndexType n] := FloatVector' .normal n

namespace FloatVector

variable
  {strg : DenseVector.Storage} {n : Type*} {_ : IndexType n}


instance : VectorType.Base (FloatVector' strg n) n Float where
  toVec x i := x.data.get (toFin i)
  zero := ⟨DenseVector.const (size n) strg 0.0⟩
  zero_spec := sorry_proof
  scal k x := ⟨x.data.scal k⟩
  scal_spec := sorry_proof
  scalAdd a b x := ⟨x.data.scalAdd a b⟩
  scalAdd_spec := sorry_proof
  sum x := x.data.sum
  sum_spec := sorry_proof
  asum x := x.data.asum
  asum_spec := sorry_proof
  nrm2 x := x.data.nrm2
  nrm2_spec := sorry_proof
  iamax x := fromFin x.data.iamax
  iamax_spec := sorry_proof
  imaxRe x h := fromFin (x.data.imaxRe (by omega))
  imaxRe_spec := sorry_proof
  iminRe x h := fromFin (x.data.iminRe (by omega))
  iminRe_spec := sorry_proof
  dot x y := x.data.dot y.data
  dot_spec := sorry_proof
  axpy a x y := ⟨DenseVector.axpy a x.data y.data⟩
  axpy_spec := sorry_proof
  axpby a x b y := ⟨DenseVector.axpby a x.data b y.data⟩
  axpby_spec := sorry_proof
  mul x y := ⟨DenseVector.mul x.data y.data⟩
  mul_spec := sorry_proof


instance : VectorType.Dense (FloatVector' strg n) where
  fromVec f := ⟨DenseVector.ofFn (fun i => f (fromFin i))⟩
  right_inv := by intro f; simp[VectorType.toVec]
  const k := ⟨DenseVector.const (size n) _ k⟩
  const_spec := sorry_proof
  div x y := ⟨x.data.div y.data⟩
  div_spec := sorry_proof
  inv x := ⟨x.data.inv⟩
  inv_spec := sorry_proof
  exp x := ⟨x.data.exp⟩
  exp_spec := sorry_proof


instance : VectorType.Lawful (FloatVector n) where
  toVec_injective := by
    intro x y h;
    cases' x with x; cases' y with y
    simp only [FloatVector'.mk.injEq]
    simp [VectorType.toVec,DenseVector.get] at h
    sorry_proof
