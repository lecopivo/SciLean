import SciLean.Data.MatrixType.Operations.ToMatrix

namespace SciLean

def_fun_prop MatrixType.fromMatrix in f [MatrixType.Lawful M] : IsLinearMap K by
  constructor <;>
  (intros; ext i;
   simp[matrix_to_spec,vector_to_spec,←MatrixType.toVec_eq_toMatrix])


def_fun_prop MatrixType.fromMatrix in f [MatrixType.Lawful M] : Continuous by
  have h : (fun x => MatrixType.fromMatrix (M:=M) x) = fun f =>ₗ[K] MatrixType.fromMatrix f := rfl
  rw[h];
  apply LinearMap.continuous_of_finiteDimensional


def_fun_prop MatrixType.fromMatrix in f [MatrixType.Lawful M] : IsContinuousLinearMap K by
  constructor
  · fun_prop
  · dsimp only [autoParam]; fun_prop


#generate_linear_map_simps MatrixType.Dense.fromMatrix.arg_f.IsLinearMap_rule


abbrev_fun_trans MatrixType.fromMatrix in f [MatrixType.Lawful M] : fderiv K by
  fun_trans


abbrev_fun_trans MatrixType.fromMatrix in f [MatrixType.Lawful M] : fwdFDeriv K by
  fun_trans


open Classical in
abbrev_fun_trans MatrixType.fromMatrix in f [MatrixType.Lawful M] : adjoint K by
  equals (fun x => MatrixType.toMatrix x) =>
    funext f
    apply AdjointSpace.ext_inner_left K
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec,matrix_to_spec,
         Finset.sum_ite, Finset.filter_eq,Inner.inner,sum_to_finset_sum,
         MatrixType.toVec_eq_toMatrix, ←Finset.univ_product_univ, Finset.sum_product]

abbrev_fun_trans MatrixType.fromMatrix in f [MatrixType.Lawful M] : revFDeriv K by
  unfold revFDeriv
  autodiff


@[data_synth]
theorem MatrixType.Base.fromMatrix.arg_f.HasRevFDerivUpdate_rule_simple
    {M : Type} {m : outParam (Type)}
    {n : outParam (Type)} {x : outParam (IndexType m)} {_ : outParam (IndexType n)} {R : outParam (Type)}
    {K : outParam (Type)} {_ : outParam (RealScalar R)} {_ : outParam (Scalar R K)} {X : outParam (Type)}
    {Y : outParam (Type)} {_ : outParam (VectorType.Base X n K)} {_ : outParam (VectorType.Base Y m K)}
    {inst : MatrixType.Base M X Y} [self : MatrixType.Dense M] [MatrixType.Lawful M] :
    HasRevFDerivUpdate K
        (MatrixType.fromMatrix (M:=M))
        (fun f => (MatrixType.fromMatrix f,
           fun dA dB i j=>
             let dAij := MatrixType.toMatrix dA i j
             dB i j + dAij)) := by
  constructor
  · fun_trans; rfl
  · fun_prop


@[data_synth]
theorem MatrixType.Base.fromMatrix.arg_f.HasRevFDerivUpdate_rule
    {M : Type} {m : outParam (Type)}
    {n : outParam (Type)} {x : outParam (IndexType m)} {_ : outParam (IndexType n)} {R : outParam (Type)}
    {K : outParam (Type)} {_ : outParam (RealScalar R)} {_ : outParam (Scalar R K)} {X : outParam (Type)}
    {Y : outParam (Type)} {_ : outParam (VectorType.Base X n K)} {_ : outParam (VectorType.Base Y m K)}
    {inst : MatrixType.Base M X Y} [self : MatrixType.Dense M] [MatrixType.Lawful M]
    {W : Type} [NormedAddCommGroup W] [AdjointSpace K W] [CompleteSpace W]
    (f : W → Matrix m n K) (f') (hf : HasRevFDerivUpdate K f f') :
    HasRevFDerivUpdate K
        (fun w => MatrixType.fromMatrix (M:=M) (f w))
        (fun w =>
           let' (A,df') := f' w
           (MatrixType.fromMatrix A,
           fun dA dw =>
             df' (MatrixType.toMatrix dA) dw)) := by
  have ⟨hf',_⟩ := hf
  constructor
  · fun_trans[hf']
  · fun_prop
