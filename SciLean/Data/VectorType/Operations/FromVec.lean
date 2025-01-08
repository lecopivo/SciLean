import SciLean.Data.VectorType.Operations.ToVec

namespace SciLean


def_fun_prop VectorType.fromVec in f [VectorType.Lawful X] : IsLinearMap K by
  constructor <;> (intros; ext i; simp[vector_to_spec])


def_fun_prop VectorType.fromVec in f [VectorType.Lawful X] : Continuous by
  have h : (fun x => VectorType.fromVec (X:=X) x) = fun f =>ₗ[K] VectorType.fromVec f := rfl
  rw[h];
  apply LinearMap.continuous_of_finiteDimensional


def_fun_prop VectorType.fromVec in f [VectorType.Lawful X] : IsContinuousLinearMap K by
  constructor
  · fun_prop
  · dsimp only [autoParam]; fun_prop


#generate_linear_map_simps VectorType.Base.toVec.arg_x.IsLinearMap_rule


abbrev_fun_trans VectorType.fromVec in f [VectorType.Lawful X] : fderiv K by
  fun_trans


abbrev_fun_trans VectorType.fromVec in f [VectorType.Lawful X] : fwdFDeriv K by
  fun_trans


open Classical in
abbrev_fun_trans VectorType.fromVec in f [VectorType.Lawful X] : adjoint K by
  equals (fun x => VectorType.toVec x) => -- todo: add specific definition for canonical basis: `VectorType.set 0 i 1`
    funext f
    apply AdjointSpace.ext_inner_left K
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec, Finset.sum_ite, Finset.filter_eq,Inner.inner,sum_to_finset_sum]


abbrev_fun_trans VectorType.fromVec in f [VectorType.Lawful X] : revFDeriv K by
  unfold revFDeriv
  autodiff


@[data_synth]
theorem VectorType.Base.fromVec.arg_f.HasRevFDerivUpdate_rule
    {X : Type} {n : (Type)} {inst : (IndexType n)} {R : (Type)}
    {K : (Type)} {inst_1 : (Scalar R R)} {inst_2 : (Scalar R K)}
    [self : VectorType.Base X n K] [inst_3 : VectorType.Lawful X] [inst_4 : VectorType.Dense X] :
    HasRevFDerivUpdate K
      (VectorType.fromVec (X:=X))
      (fun f => (VectorType.fromVec f,
        fun dk dx i => dx i + VectorType.toVec dk i)) := by
  constructor
  · intros
    fun_trans
    funext dk dx j
    simp
  · fun_prop
