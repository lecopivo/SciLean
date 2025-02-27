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
  [self : MatrixType.Base M X Y] [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] [InjectiveGetElem Y m]


omit [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] in
@[simp, simp_core]
theorem MatrixType.gemv_zero_alpha (b : K) (A : M) (x : X) (y : Y) :
    MatrixType.gemv 0 b A x y = b•y := by
  ext i; simp[vector_to_spec,matrix_to_spec]

omit [InjectiveGetElem X n] in
@[simp, simp_core]
theorem MatrixType.gemv_zero_A (a b : K) (x : X) (y : Y) :
    MatrixType.gemv a b (0:M) x y = b•y := by
  ext i; simp[vector_to_spec,matrix_to_spec]

omit [InjectiveGetElem M (m×n)] in
@[simp, simp_core]
theorem MatrixType.gemv_zero_x (a b : K) (A : M) (y : Y) :
    MatrixType.gemv a b A 0 y = b•y := by
  ext i; simp[vector_to_spec,matrix_to_spec,Matrix.mulVec]

end Simps


namespace GemvImpl
-- local macro does not work for some reason, so we use scoped macro
scoped macro "linearity_proof" : tactic =>
  `(tactic|
    (apply (IsContinuousLinearMap.injective_comp_iff VectorType.toVec (by fun_prop) (getElem_injective)).2
     simp +unfoldPartialApp [vector_to_spec, Matrix.mulVec, dotProduct,VectorType.toVec]
     fun_prop))
end GemvImpl
open GemvImpl

-- All possible combinations or arguments that makes `gemv` a linear function
def_fun_prop MatrixType.gemv in alpha beta [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    IsContinuousLinearMap K by linearity_proof

def_fun_prop MatrixType.gemv in alpha y [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    IsContinuousLinearMap K by linearity_proof

def_fun_prop MatrixType.gemv in A beta [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    IsContinuousLinearMap K by linearity_proof

def_fun_prop MatrixType.gemv in A y [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    IsContinuousLinearMap K by linearity_proof

def_fun_prop MatrixType.gemv in x beta [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    IsContinuousLinearMap K by linearity_proof

def_fun_prop MatrixType.gemv in x y [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    IsContinuousLinearMap K by linearity_proof

-- Differentiable
def_fun_prop MatrixType.gemv in alpha beta A x y
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    Differentiable K by
  apply (Differentiable.injective_comp_iff VectorType.toVec (by fun_prop) (getElem_injective)).2
  simp +unfoldPartialApp [matrix_to_spec, vector_to_spec, Matrix.mulVec, dotProduct,VectorType.toVec]
  fun_prop

-- fderiv
abbrev_fun_trans MatrixType.gemv in alpha beta A x y
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    fderiv K by
  equals (fun x => ContinuousLinearMap.mk' K (fun dx =>
    let' (a,b,A,x,y) := x
    let' (da,db,dA,dx,dy) := dx
    let dz₁ := MatrixType.gemv a b A dx dy
    let dz₂ := MatrixType.gemv da db A x y
    MatrixType.gemv a (1:K) dA x (dz₁+dz₂)) (by simp; fun_prop)) => sorry_proof

abbrev_fun_trans MatrixType.gemv in alpha beta A x y -- arg_subsets -- too slow :(
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    fwdFDeriv K by
  unfold fwdFDeriv
  autodiff; to_ssa

abbrev_data_synth MatrixType.gemv in A x y
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] [InjectiveGetElem Y m] (Axy₀) :
    (HasFDerivAt (𝕜:=K) · · Axy₀) by
  apply hasFDerivAt_from_fderiv
  case deriv => conv => rhs; fun_trans
  case diff => dsimp [autoParam]; fun_prop

-- argument subset - todo: automate this!
abbrev_data_synth MatrixType.gemv in A x
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] [InjectiveGetElem Y m] (Axy₀) :
    (HasFDerivAt (𝕜:=K) · · Axy₀) by
  apply hasFDerivAt_from_hasFDerivAt
  case deriv =>
    apply hasFDerivAt_comp
              (g:=fun Ax : M×X => (Ax.1,Ax.2,y))
              (f:=fun Axy : M×X×Y => MatrixType.gemv alpha beta Axy.1 Axy.2.1 Axy.2.2)
              (hg:=by data_synth)
              (hf:=by data_synth)
  case simp => conv =>
    rhs; lsimp

-- argument subset - todo: automate this!
abbrev_data_synth MatrixType.gemv in A y
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] [InjectiveGetElem Y m] (Axy₀) :
    (HasFDerivAt (𝕜:=K) · · Axy₀) by
  apply hasFDerivAt_from_hasFDerivAt
  case deriv =>
    apply hasFDerivAt_comp
              (g:=fun Ay : M×Y => (Ay.1,x,Ay.2))
              (f:=fun Axy : M×X×Y => MatrixType.gemv alpha beta Axy.1 Axy.2.1 Axy.2.2)
              (hg:=by data_synth)
              (hf:=by data_synth)
  case simp => conv => rhs; lsimp

-- argument subset - todo: automate this!
abbrev_data_synth MatrixType.gemv in x y
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] [InjectiveGetElem Y m] (Axy₀) :
    (HasFDerivAt (𝕜:=K) · · Axy₀) by
  apply hasFDerivAt_from_hasFDerivAt
  case deriv =>
    apply hasFDerivAt_comp
              (g:=fun xy : X×Y => (A,xy.1,xy.2))
              (f:=fun Axy : M×X×Y => MatrixType.gemv alpha beta Axy.1 Axy.2.1 Axy.2.2)
              (hg:=by data_synth)
              (hf:=by data_synth)
  case simp => conv => rhs; lsimp

-- argument subset - todo: automate this!
abbrev_data_synth MatrixType.gemv in A
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] [InjectiveGetElem Y m] (Axy₀) :
    (HasFDerivAt (𝕜:=K) · · Axy₀) by
  apply hasFDerivAt_from_hasFDerivAt
  case deriv =>
    apply hasFDerivAt_comp
              (g:=fun A : M => (A,x,y))
              (f:=fun Axy : M×X×Y => MatrixType.gemv alpha beta Axy.1 Axy.2.1 Axy.2.2)
              (hg:=by data_synth)
              (hf:=by data_synth)
  case simp => conv => rhs; lsimp

-- argument subset - todo: automate this!
abbrev_data_synth MatrixType.gemv in x
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] [InjectiveGetElem Y m] (Axy₀) :
    (HasFDerivAt (𝕜:=K) · · Axy₀) by
  apply hasFDerivAt_from_hasFDerivAt
  case deriv =>
    apply hasFDerivAt_comp
              (g:=fun x : X => (A,x,y))
              (f:=fun Axy : M×X×Y => MatrixType.gemv alpha beta Axy.1 Axy.2.1 Axy.2.2)
              (hg:=by data_synth)
              (hf:=by data_synth)
  case simp => conv => rhs; lsimp

-- argument subset - todo: automate this!
abbrev_data_synth MatrixType.gemv in y
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] [InjectiveGetElem Y m] (Axy₀) :
    (HasFDerivAt (𝕜:=K) · · Axy₀) by
  apply hasFDerivAt_from_hasFDerivAt
  case deriv =>
    apply hasFDerivAt_comp
              (g:=fun y : Y => (A,x,y))
              (f:=fun Axy : M×X×Y => MatrixType.gemv alpha beta Axy.1 Axy.2.1 Axy.2.2)
              (hg:=by data_synth)
              (hf:=by data_synth)
  case simp => conv => rhs; lsimp

-- forward AD
abbrev_fun_trans MatrixType.gemv in A x y
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    fwdFDeriv K by
  unfold fwdFDeriv
  autodiff; to_ssa

open ComplexConjugate in
abbrev_fun_trans MatrixType.gemv in x y
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
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
    [InjectiveGetElem M (m×n)] [MatrixType.Dense M] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
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
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    adjoint K by
  equals (fun z => (VectorType.dot (MatrixType.gemv 1 0 A x 0) z, VectorType.dot y z)) =>
    funext z
    apply AdjointSpace.ext_inner_left K
    intro x
    rw[← adjoint_ex _ (by fun_prop)]
    -- simp +unfoldPartialApp [vector_to_spec, matrix_to_spec, sum_pull,Inner.inner,
    --      Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    sorry_proof

open ComplexConjugate
abbrev_data_synth MatrixType.gemv in x y
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    HasAdjoint K by
  conv => enter[3]; assign (fun z => (MatrixType.gemvH (conj alpha) 0 A z 0,
                                      VectorType.scal (conj beta) z))
  sorry_proof

open ComplexConjugate
abbrev_data_synth MatrixType.gemv in x y
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    HasAdjointUpdate K by
  apply hasAdjointUpdate_from_hasAdjoint
  case adjoint => data_synth
  case simp => intros; conv => rhs; simp[Prod.add_def,vector_optimize]

open ComplexConjugate
abbrev_data_synth MatrixType.gemv in A y
    [InjectiveGetElem M (m×n)] [MatrixType.Dense M] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    HasAdjoint K by
  conv => enter[3]; assign (fun z : Y => (MatrixType.outerprodAdd (conj alpha) z x (0:M),
                                          VectorType.scal (conj beta) z))
  sorry_proof

abbrev_data_synth MatrixType.gemv in A y
    [InjectiveGetElem M (m×n)] [MatrixType.Dense M] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    HasAdjointUpdate K by
  apply hasAdjointUpdate_from_hasAdjoint
  case adjoint => data_synth
  case simp => intros; conv => rhs; simp[Prod.add_def,vector_optimize]


-- reverse AD
abbrev_fun_trans MatrixType.gemv in alpha beta A x y
    [InjectiveGetElem M (m×n)] [MatrixType.Dense M] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    revFDeriv K by
  unfold revFDeriv
  fun_trans

abbrev_fun_trans MatrixType.gemv in A x y
    [InjectiveGetElem M (m×n)] [MatrixType.Dense M] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    revFDeriv K by
  unfold revFDeriv
  fun_trans

abbrev_data_synth MatrixType.gemv in A x y
    [InjectiveGetElem M (m×n)] [MatrixType.Dense M] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    HasRevFDeriv K by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intros; dsimp; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => conv => rhs; lsimp

abbrev_data_synth MatrixType.gemv in A x y
    [InjectiveGetElem M (m×n)] [MatrixType.Dense M] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    HasRevFDerivUpdate K by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intros; dsimp; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => conv => rhs; simp[vector_optimize]; to_ssa; to_ssa; lsimp

-- argument subset - todo: automate this!
abbrev_data_synth MatrixType.gemv in A x
    [InjectiveGetElem M (m×n)] [MatrixType.Dense M] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    HasRevFDeriv K by
  apply hasRevFDeriv_from_hasRevFDeriv
  case deriv =>
    apply HasRevFDeriv.comp_rule
            (g:=fun Ax : M×X => (Ax.1,Ax.2,y))
            (f:=fun Axy : M×X×Y => MatrixType.gemv alpha beta Axy.1 Axy.2.1 Axy.2.2)
            (hg:=by data_synth)
            (hf:=by data_synth)
  case simp =>
    conv => rhs; lsimp

-- argument subset - todo: automate this!
abbrev_data_synth MatrixType.gemv in A x
    [InjectiveGetElem M (m×n)] [MatrixType.Dense M] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    HasRevFDerivUpdate K by
  apply hasRevFDerivUpdate_from_hasRevFDerivUpdate
  case deriv =>
    apply HasRevFDerivUpdate.comp_rule
            (g:=fun Ax : M×X => (Ax.1,Ax.2,y))
            (f:=fun Axy : M×X×Y => MatrixType.gemv alpha beta Axy.1 Axy.2.1 Axy.2.2)
            (hg:=by data_synth)
            (hf:=by data_synth)
  case simp =>
    conv => rhs; simp[vector_optimize]; to_ssa; to_ssa; lsimp

-- argument subset - todo: automate this!
abbrev_data_synth MatrixType.gemv in x
    [InjectiveGetElem M (m×n)] [MatrixType.Dense M] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    HasRevFDeriv K by
  apply hasRevFDeriv_from_hasRevFDeriv
  case deriv =>
    apply HasRevFDeriv.comp_rule
            (g:=fun x : X => (A,x,y))
            (f:=fun Axy : M×X×Y => MatrixType.gemv alpha beta Axy.1 Axy.2.1 Axy.2.2)
            (hg:=by data_synth)
            (hf:=by data_synth)
  case simp =>
    conv => rhs; lsimp

-- argument subset - todo: automate this!
abbrev_data_synth MatrixType.gemv in x
    [InjectiveGetElem M (m×n)] [MatrixType.Dense M] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    HasRevFDerivUpdate K by
  apply hasRevFDerivUpdate_from_hasRevFDerivUpdate
  case deriv =>
    apply HasRevFDerivUpdate.comp_rule
            (g:=fun x : X => (A,x,y))
            (f:=fun Axy : M×X×Y => MatrixType.gemv alpha beta Axy.1 Axy.2.1 Axy.2.2)
            (hg:=by data_synth)
            (hf:=by data_synth)
  case simp =>
    conv => rhs; simp[vector_optimize]; to_ssa; to_ssa; lsimp

-- argument subset - todo: automate this!
abbrev_data_synth MatrixType.gemv in y
    [InjectiveGetElem M (m×n)] [MatrixType.Dense M] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    HasRevFDeriv K by
  apply hasRevFDeriv_from_hasRevFDeriv
  case deriv =>
    apply HasRevFDeriv.comp_rule
            (g:=fun y : Y => (A,x,y))
            (f:=fun Axy : M×X×Y => MatrixType.gemv alpha beta Axy.1 Axy.2.1 Axy.2.2)
            (hg:=by data_synth)
            (hf:=by data_synth)
  case simp =>
    conv => rhs; lsimp

-- argument subset - todo: automate this!
abbrev_data_synth MatrixType.gemv in y
    [InjectiveGetElem M (m×n)] [MatrixType.Dense M] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    HasRevFDerivUpdate K by
  apply hasRevFDerivUpdate_from_hasRevFDerivUpdate
  case deriv =>
    apply HasRevFDerivUpdate.comp_rule
            (g:=fun y : Y => (A,x,y))
            (f:=fun Axy : M×X×Y => MatrixType.gemv alpha beta Axy.1 Axy.2.1 Axy.2.2)
            (hg:=by data_synth)
            (hf:=by data_synth)
  case simp =>
    conv => rhs; simp[vector_optimize]; to_ssa; to_ssa; lsimp

-- argument subset - todo: automate this!
abbrev_data_synth MatrixType.gemv in A
    [InjectiveGetElem M (m×n)] [MatrixType.Dense M] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    HasRevFDeriv K by
  apply hasRevFDeriv_from_hasRevFDeriv
  case deriv =>
    apply HasRevFDeriv.comp_rule
            (g:=fun A : M => (A,x,y))
            (f:=fun Axy : M×X×Y => MatrixType.gemv alpha beta Axy.1 Axy.2.1 Axy.2.2)
            (hg:=by data_synth)
            (hf:=by data_synth)
  case simp =>
    conv => rhs; lsimp

-- argument subset - todo: automate this!
abbrev_data_synth MatrixType.gemv in A
    [InjectiveGetElem M (m×n)] [MatrixType.Dense M] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    HasRevFDerivUpdate K by
  apply hasRevFDerivUpdate_from_hasRevFDerivUpdate
  case deriv =>
    apply HasRevFDerivUpdate.comp_rule
            (g:=fun A : M => (A,x,y))
            (f:=fun Axy : M×X×Y => MatrixType.gemv alpha beta Axy.1 Axy.2.1 Axy.2.2)
            (hg:=by data_synth)
            (hf:=by data_synth)
  case simp =>
    conv => rhs; simp[vector_optimize]; to_ssa; to_ssa; lsimp


----------------------------------------------------------------------------------------------------
-- HMul notation -----------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[fun_prop]
theorem HMul.hMul.arg_a0a1.Differentiable_rule_matVec_mul.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} {M : Type u_1} {m : Type u_2}
  {n : Type u_3} [IndexType m] [IndexType n] {R : Type u_4} {K : Type u_5} [RealScalar R] [Scalar R K] {X : Type u_6}
  {Y : Type u_7} [VectorType.Base X n K] [VectorType.Base Y m K] [MatrixType.Base M X Y] [InjectiveGetElem M (m × n)]
  [MatrixType.Dense M] [InjectiveGetElem X n] [InjectiveGetElem Y m] :
  Differentiable K (fun Ax : M×X => Ax.1 * Ax.2) := by simp[HMul.hMul]; fun_prop

@[fun_trans]
theorem _root_.HMul.hMul.arg_a0a1.revFDeriv_rule_matVec_mul
    {M m n : Type*} [IndexType m] [IndexType n]
    {R K : Type*} [RealScalar R] [Scalar R K]
    {X Y : Type*} [VectorType.Base X n K] [VectorType.Base Y m K]
    [MatrixType.Base M X Y] [InjectiveGetElem M (m×n)] [MatrixType.Dense M]
    [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    revFDeriv K (fun Ax : M×X => Ax.1 * Ax.2)
    =
    fun Ax =>
      let' (A,x) := Ax
      (A*x, fun dy =>
        let dA := MatrixType.Dense.outerprodAdd 1 dy x (0:M)
        let dx := MatrixType.Base.gemvH 1 0 A dy (0:X)
        (dA,dx)) := by
  simp[HMul.hMul]
  fun_trans

@[data_synth]
theorem _root_.HMul.hMul.arg_a0a1.HasRevFDeriv_rule_matVec_mul
    {M m n : Type*} [IndexType m] [IndexType n]
    {R K : Type*} [RealScalar R] [Scalar R K]
    {X Y : Type*} [VectorType.Base X n K] [VectorType.Base Y m K]
    [MatrixType.Base M X Y] [InjectiveGetElem M (m×n)] [MatrixType.Dense M]
    [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    HasRevFDeriv K
      (fun Ax : M×X => Ax.1 * Ax.2)
      (fun Ax =>
        let' (A,x) := Ax
        (A*x, fun dy =>
          let dA := MatrixType.Dense.outerprodAdd 1 dy x (0:M)
          let dx := MatrixType.Base.gemvH 1 0 A dy (0:X)
          (dA,dx))) := by
  sorry_proof -- some issue computing `HasFDerivAt` here
  -- apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  -- simp [HMul.hMul]
  -- case deriv => intros; data_synth -- some problem assigning the result, has to be a bug in `data_synth`
  -- case adjoint => sorry
  -- case simp => sorry

-- argument subset - todo: automate this!
@[data_synth]
theorem _root_.HMul.hMul.arg_a0.HasRevFDeriv_rule_matVec_mul
    {M m n : Type*} [IndexType m] [IndexType n]
    {R K : Type*} [RealScalar R] [Scalar R K]
    {X Y : Type*} [VectorType.Base X n K] [VectorType.Base Y m K]
    [MatrixType.Base M X Y] [InjectiveGetElem M (m×n)] [MatrixType.Dense M]
    [InjectiveGetElem X n] [InjectiveGetElem Y m] (x : X) :
    HasRevFDeriv K
      (fun A : M => A * x)
      (fun A =>
        (A*x, fun dy =>
          let dA := MatrixType.Dense.outerprodAdd 1 dy x (0:M)
          dA)) := by
  apply hasRevFDeriv_from_hasRevFDeriv
  case deriv =>
    apply HasRevFDeriv.comp_rule
            (g:=fun A : M => (A,x))
            (f:=fun Ax : M×X => Ax.1 * Ax.2)
            (hg:=by data_synth)
            (hf:=by data_synth)
  case simp => simp

-- argument subset - todo: automate this!
@[data_synth]
theorem _root_.HMul.hMul.arg_a1.HasRevFDeriv_rule_matVec_mul
    {M m n : Type*} [IndexType m] [IndexType n]
    {R K : Type*} [RealScalar R] [Scalar R K]
    {X Y : Type*} [VectorType.Base X n K] [VectorType.Base Y m K]
    [MatrixType.Base M X Y] [InjectiveGetElem M (m×n)] [MatrixType.Dense M]
    [InjectiveGetElem X n] [InjectiveGetElem Y m] (A : M) :
    HasRevFDeriv K
      (fun x : X => A * x)
      (fun x =>
        (A*x, fun dy =>
          let dx := MatrixType.Base.gemvH 1 0 A dy (0:X)
          dx)) := by
  apply hasRevFDeriv_from_hasRevFDeriv
  case deriv =>
    apply HasRevFDeriv.comp_rule
            (g:=fun x : X => (A,x))
            (f:=fun Ax : M×X => Ax.1 * Ax.2)
            (hg:=by data_synth)
            (hf:=by data_synth)
  case simp => simp


@[data_synth]
theorem _root_.HMul.hMul.arg_a0a1.HasRevFDerivUpdate_rule_matVec_mul
    {M m n : Type*} [IndexType m] [IndexType n]
    {R K : Type*} [RealScalar R] [Scalar R K]
    {X Y : Type*} [VectorType.Base X n K] [VectorType.Base Y m K]
    [MatrixType.Base M X Y] [InjectiveGetElem M (m×n)] [MatrixType.Dense M]
    [InjectiveGetElem X n] [InjectiveGetElem Y m] :
    HasRevFDerivUpdate K
      (fun Ax : M×X => Ax.1 * Ax.2)
      (fun Ax =>
        let' (A,x) := Ax
        (A*x, fun dy dAx =>
          let' (dA,dx) := dAx
          let dA := MatrixType.Dense.outerprodAdd 1 dy x dA
          let dx := MatrixType.Base.gemvH 1 1 A dy dx
          (dA,dx))) := by
  sorry_proof -- some issue computing `HasFDerivUpdateAt` here
  -- apply hasRevFDerivUpdate_from_hasFDerivUpdateAt_hasAdjoint
  -- simp [HMul.hMul]
  -- case derivUpdate => intros; data_synth -- some problem assigning the result, has to be a bug in `data_synth`
  -- case adjoint => sorry
  -- case simp => sorry

-- argument subset - todo: automate this!
@[data_synth]
theorem _root_.HMul.hMul.arg_a0.HasRevFDerivUpdate_rule_matVec_mul
    {M m n : Type*} [IndexType m] [IndexType n]
    {R K : Type*} [RealScalar R] [Scalar R K]
    {X Y : Type*} [VectorType.Base X n K] [VectorType.Base Y m K]
    [MatrixType.Base M X Y] [InjectiveGetElem M (m×n)] [MatrixType.Dense M]
    [InjectiveGetElem X n] [InjectiveGetElem Y m] (x : X) :
    HasRevFDerivUpdate K
      (fun A : M => A * x)
      (fun A =>
        (A*x, fun dy dA =>
          let dA := MatrixType.Dense.outerprodAdd 1 dy x dA
          dA)) := by
  apply hasRevFDerivUpdate_from_hasRevFDerivUpdate
  case deriv =>
    apply HasRevFDerivUpdate.comp_rule
            (g:=fun A : M => (A,x))
            (f:=fun Ax : M×X => Ax.1 * Ax.2)
            (hg:=by data_synth)
            (hf:=by data_synth)
  case simp =>
    funext A; simp; funext dy dA; ext ⟨i,j⟩
    simp[vector_to_spec]; ac_rfl

-- argument subset - todo: automate this!
@[data_synth]
theorem _root_.HMul.hMul.arg_a1.HasRevFDerivUpdate_rule_matVec_mul
    {M m n : Type*} [IndexType m] [IndexType n]
    {R K : Type*} [RealScalar R] [Scalar R K]
    {X Y : Type*} [VectorType.Base X n K] [VectorType.Base Y m K]
    [MatrixType.Base M X Y] [InjectiveGetElem M (m×n)] [MatrixType.Dense M]
    [InjectiveGetElem X n] [InjectiveGetElem Y m] (A : M) :
    HasRevFDerivUpdate K
      (fun x : X => A * x)
      (fun x =>
        (A*x, fun dy dx =>
          let dx := MatrixType.Base.gemvH 1 1 A dy dx
          dx)) := by
  apply hasRevFDerivUpdate_from_hasRevFDerivUpdate
  case deriv =>
    apply HasRevFDerivUpdate.comp_rule
            (g:=fun x : X => (A,x))
            (f:=fun Ax : M×X => Ax.1 * Ax.2)
            (hg:=by data_synth)
            (hf:=by data_synth)
  case simp =>
    funext A; simp; funext dy dx; ext i; simp
    simp [vector_to_spec]; ac_rfl
