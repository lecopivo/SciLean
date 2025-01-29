import SciLean.Data.MatrixType.Base
import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.Analysis.Calculus.FwdFDeriv
-- import SciLean.Tactic.DataSynth.HasRevFDerivUpdate
import SciLean.Data.VectorType.Operations.Scal
import SciLean.Data.VectorType.Operations.Mul
import SciLean.Data.MatrixType.Operations.ToMatrix
import SciLean.Data.VectorType.Optimize
import SciLean.Data.MatrixType.Optimize
import SciLean.Lean.ToSSA

namespace SciLean


section Simps

variable
  {M : Type u_1} {m : outParam (Type u_2)}
  {n : outParam (Type u_3)} {_: IndexType m} {_ : IndexType n} {R : outParam (Type u_4)}
  {K : outParam (Type u_5)} {_ : RealScalar R} {_ : Scalar R K} {X : outParam (Type u_6)}
  {Y : outParam (Type u_7)} {_ : VectorType.Base X n K} {_ : VectorType.Base Y m K}
  [self : MatrixType.Base M X Y] [VectorType.Lawful M] [VectorType.Lawful X] [VectorType.Lawful Y]


omit [VectorType.Lawful M] [VectorType.Lawful X] in
@[simp, simp_core]
theorem MatrixType.gemv_zero_alpha (b : K) (A : M) (x : X) (y : Y) :
    MatrixType.gemv 0 b A x y = b•y := by
  ext i; simp[vector_to_spec,matrix_to_spec]

omit [VectorType.Lawful X] in
@[simp, simp_core]
theorem MatrixType.gemv_zero_A (a b : K) (x : X) (y : Y) :
    MatrixType.gemv a b (0:M) x y = b•y := by
  ext i; simp[vector_to_spec,matrix_to_spec]

omit [VectorType.Lawful M] in
@[simp, simp_core]
theorem MatrixType.gemv_zero_x (a b : K) (A : M) (y : Y) :
    MatrixType.gemv a b A 0 y = b•y := by
  ext i; simp[vector_to_spec,matrix_to_spec]

end Simps


namespace GemvImpl
-- local macro does not work for some reason, so we use scoped macro
scoped macro "linearity_proof" : tactic =>
  `(tactic|
    (apply (IsContinuousLinearMap.injective_comp_iff VectorType.toVec (by fun_prop) (VectorType.Lawful.toVec_injective)).2
     simp +unfoldPartialApp [vector_to_spec, Matrix.mulVec, dotProduct]
     fun_prop))
end GemvImpl
open GemvImpl

-- All possible combinations or arguments that makes `gemv` a linear function
def_fun_prop MatrixType.gemv in alpha beta [VectorType.Lawful M] [VectorType.Lawful X] [VectorType.Lawful Y] :
    IsContinuousLinearMap K by linearity_proof

def_fun_prop MatrixType.gemv in alpha y [VectorType.Lawful M] [VectorType.Lawful X] [VectorType.Lawful Y] :
    IsContinuousLinearMap K by linearity_proof

def_fun_prop MatrixType.gemv in A beta [VectorType.Lawful M] [VectorType.Lawful X] [VectorType.Lawful Y] :
    IsContinuousLinearMap K by linearity_proof

def_fun_prop MatrixType.gemv in A y [VectorType.Lawful M] [VectorType.Lawful X] [VectorType.Lawful Y] :
    IsContinuousLinearMap K by linearity_proof

def_fun_prop MatrixType.gemv in x beta [VectorType.Lawful M] [VectorType.Lawful X] [VectorType.Lawful Y] :
    IsContinuousLinearMap K by linearity_proof

def_fun_prop MatrixType.gemv in x y [VectorType.Lawful M] [VectorType.Lawful X] [VectorType.Lawful Y] :
    IsContinuousLinearMap K by linearity_proof

-- Differentiable
def_fun_prop MatrixType.gemv in alpha beta A x y
    [VectorType.Lawful M] [VectorType.Lawful X] [VectorType.Lawful Y] :
    Differentiable K by
  apply (Differentiable.injective_comp_iff VectorType.toVec (by fun_prop) (VectorType.Lawful.toVec_injective)).2
  simp +unfoldPartialApp [matrix_to_spec, vector_to_spec, Matrix.mulVec, dotProduct]
  fun_prop

abbrev_fun_trans MatrixType.gemv in alpha beta A x y
    [VectorType.Lawful M] [VectorType.Lawful X] [VectorType.Lawful Y] :
    fderiv K by
  equals (fun x => ContinuousLinearMap.mk' K (fun dx =>
    let' (a,b,A,x,y) := x
    let' (da,db,dA,dx,dy) := dx
    let dz₁ := MatrixType.gemv a b A dx dy
    let dz₂ := MatrixType.gemv da db A x y
    MatrixType.gemv a (1:K) dA x (dz₁+dz₂)) (by simp; fun_prop)) => sorry_proof

abbrev_fun_trans MatrixType.gemv in alpha beta A x y -- arg_subsets -- too slow :(
    [VectorType.Lawful M] [VectorType.Lawful X] [VectorType.Lawful Y] :
    fwdFDeriv K by
  unfold fwdFDeriv
  autodiff; to_ssa


abbrev_fun_trans MatrixType.gemv in A x y
    [VectorType.Lawful M] [VectorType.Lawful X] [VectorType.Lawful Y] :
    fwdFDeriv K by
  unfold fwdFDeriv
  autodiff; to_ssa

open ComplexConjugate in
abbrev_fun_trans MatrixType.gemv in x y
    [VectorType.Lawful M] [VectorType.Lawful X] [VectorType.Lawful Y] :
    adjoint K by
  equals (fun z => (MatrixType.gemvH (conj alpha) 0 A z 0, VectorType.scal (conj beta) z)) =>
    funext z
    apply AdjointSpace.ext_inner_left K
    intro x
    rw[← adjoint_ex _ (by fun_prop)]
    -- simp +unfoldPartialApp [vector_to_spec, matrix_to_spec, sum_pull,Inner.inner,
    --      Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    sorry_proof

open ComplexConjugate in
abbrev_fun_trans MatrixType.gemv in A y
    [VectorType.Lawful M] [MatrixType.Dense M] [VectorType.Lawful X] [VectorType.Lawful Y] :
    adjoint K by
  equals (fun z => (MatrixType.outerprodAdd (conj alpha) z x 0, VectorType.scal (conj beta) z)) =>
    funext z
    apply AdjointSpace.ext_inner_left K
    intro x
    rw[← adjoint_ex _ (by fun_prop)]
    -- simp +unfoldPartialApp [vector_to_spec, matrix_to_spec, sum_pull,Inner.inner,
    --      Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    sorry_proof

abbrev_fun_trans MatrixType.gemv in alpha beta
    [VectorType.Lawful M] [VectorType.Lawful X] [VectorType.Lawful Y] :
    adjoint K by
  equals (fun z => (VectorType.dot (MatrixType.gemv 1 0 A x 0) z, VectorType.dot y z)) =>
    funext z
    apply AdjointSpace.ext_inner_left K
    intro x
    rw[← adjoint_ex _ (by fun_prop)]
    -- simp +unfoldPartialApp [vector_to_spec, matrix_to_spec, sum_pull,Inner.inner,
    --      Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    sorry_proof



abbrev_fun_trans MatrixType.gemv in alpha beta A x y
    [VectorType.Lawful M] [MatrixType.Dense M] [VectorType.Lawful X] [VectorType.Lawful Y] :
    revFDeriv K by
  unfold revFDeriv
  fun_trans

abbrev_fun_trans MatrixType.gemv in A x y
    [VectorType.Lawful M] [MatrixType.Dense M] [VectorType.Lawful X] [VectorType.Lawful Y] :
    revFDeriv K by
  unfold revFDeriv
  fun_trans


-- def_rev_deriv MatrixType.gemv in alpha beta A x y
--   [VectorType.Lawful M] [VectorType.Lawful M] [MatrixType.Dense M] [VectorType.Lawful X] [VectorType.Lawful Y] by
--   constructor
--   · intro x
--     conv =>
--       rhs; dsimp
--       autodiff
--       simp [Prod.add_def, vector_optimize,VectorType.scal_one]
--   · fun_prop

-- def_rev_deriv MatrixType.gemv in A x y
--   [VectorType.Lawful M] [VectorType.Lawful M] [MatrixType.Dense M] [VectorType.Lawful X] [VectorType.Lawful Y] by
--   constructor
--   · intro x
--     conv =>
--       rhs; dsimp
--       autodiff
--       simp [Prod.add_def, vector_optimize]
--   · fun_prop


-- def_rev_deriv' MatrixType.gemv in A x
--   [VectorType.Lawful M] [VectorType.Lawful M] [MatrixType.Dense M] [VectorType.Lawful X] [VectorType.Lawful Y] by
--   have := hA.2
--   have := hx.2
--   have : revFDeriv K A
--          =
--          fun w =>
--            let' (A,dA) := A' w
--            (A, (dA · 0)) := by simp[hA.1]; rfl
--   have : revFDeriv K x
--          =
--          fun w =>
--            let' (x,dx) := x' w
--            (x, (dx · 0)) := by simp[hx.1]; rfl
--   constructor
--   · intro x
--     conv =>
--       rhs; dsimp
--       autodiff
--       simp [Prod.add_def, vector_optimize]; to_ssa; lsimp
--   · fun_prop
