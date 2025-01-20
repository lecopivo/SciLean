import SciLean.Data.VectorType.Base
import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Tactic.DataSynth.HasRevFDerivUpdate
import SciLean.Tactic.DataSynth.DefRevDeriv
-- import SciLean.Analysis.Normed.IsContinuousLinearMap

import SciLean.Meta.GenerateFunTrans

namespace SciLean


def_fun_prop VectorType.toVec in x [VectorType.Lawful X] : IsLinearMap K by
  constructor <;> (intros; simp[vector_to_spec])

def_fun_prop VectorType.toVec in x
    add_suffix _real
    [ScalarSMul R K] [ScalarInner R K] [VectorType.Lawful X] [VectorType.RealOp X] :
    IsLinearMap R by
  apply IsLinearMap.restrictScalars (S:=K)
  fun_prop


def_fun_prop VectorType.toVec in x [VectorType.Lawful X] : Continuous by
  rename_i i _
  have h : (fun x => VectorType.toVec (X:=X) x i) = fun x =>ₗ[K] VectorType.toVec x i := rfl
  rw[h];
  apply LinearMap.continuous_of_finiteDimensional


def_fun_prop VectorType.Base.toVec in x [VectorType.Lawful X] : IsContinuousLinearMap K by
  constructor
  · fun_prop
  · dsimp only [autoParam]; fun_prop

def_fun_prop VectorType.Base.toVec in x
    add_suffix _real
    [ScalarSMul R K] [ScalarInner R K] [VectorType.Lawful X] [VectorType.RealOp X] :
    IsContinuousLinearMap R by
  constructor
  · fun_prop
  · dsimp only [autoParam]; fun_prop


#generate_linear_map_simps VectorType.Base.toVec.arg_x.IsLinearMap_rule


abbrev_fun_trans VectorType.toVec in x [VectorType.Lawful X] : fderiv K by
  fun_trans

abbrev_fun_trans VectorType.toVec in x
    add_suffix _real [ScalarSMul R K] [ScalarInner R K] [VectorType.Lawful X] [VectorType.RealOp X] : fderiv R by
  fun_trans

abbrev_fun_trans VectorType.toVec in x [VectorType.Lawful X] : fwdFDeriv K by
  fun_trans

abbrev_fun_trans VectorType.toVec in x
    add_suffix _real
    [ScalarSMul R K] [ScalarInner R K] [VectorType.Lawful X] [VectorType.RealOp X] : fwdFDeriv R by
  fun_trans


open Classical in
abbrev_fun_trans VectorType.toVec in x [VectorType.Lawful X] [VectorType.Dense X] : adjoint K by
  tactic => rename_i i _ _
  equals (fun k => VectorType.set 0 i k) => -- todo: add specific definition for canonical basis: `VectorType.set 0 i 1`
    funext x
    apply AdjointSpace.ext_inner_left K
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec, Finset.sum_ite, Finset.filter_eq]


abbrev_fun_trans VectorType.toVec in x [VectorType.Lawful X] [VectorType.Dense X] : revFDeriv K by
  unfold revFDeriv
  autodiff


@[data_synth]
theorem VectorType.Base.toVec.arg_x.HasRevFDerivUpdate_rule
    {X : Type} {n : (Type)} {inst : (IndexType n)} {R : (Type)}
    {K : (Type)} {inst_1 : (RealScalar R)} {inst_2 : (Scalar R K)}
    [self : VectorType.Base X n K] [inst_3 : VectorType.Lawful X] [inst_4 : VectorType.Dense X]
    (i : n) :
    HasRevFDerivUpdate K
      (VectorType.toVec (X:=X) · i)
      (fun x => (VectorType.toVec x i,
        fun dk dx => VectorType.updateElem dx i (· + dk))) := by
  constructor
  · intros
    fun_trans
    funext dk dx
    apply VectorType.Lawful.toVec_injective
    funext j
    by_cases j = i <;> simp_all[vector_to_spec,updateElem]
  · fun_prop
