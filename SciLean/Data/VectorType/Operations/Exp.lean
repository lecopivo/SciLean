import SciLean.Data.VectorType.Operations.Scal
import SciLean.Data.VectorType.Operations.Mul
import SciLean.Analysis.SpecialFunctions.Exp

namespace SciLean

section Simps

def_fun_prop VectorType.exp in x with_transitive [VectorType.Lawful X] : Differentiable K by
  apply (Differentiable.injective_comp_iff VectorType.toVec (by fun_prop) (VectorType.Lawful.toVec_injective)).2
  simp[vector_to_spec]
  fun_prop

abbrev_fun_trans VectorType.exp in x [VectorType.Lawful X] : fderiv K by
  equals (fun x => fun dx =>L[K] VectorType.mul dx (VectorType.exp x)) =>
    funext x; ext dx : 1
    apply VectorType.Lawful.toVec_injective; funext i
    rw[toVec_fderiv (hf:=by fun_prop)]; simp [vector_to_spec]
    fun_trans

abbrev_fun_trans VectorType.exp in x [VectorType.Lawful X] : fwdFDeriv K by
  unfold fwdFDeriv
  autodiff; to_ssa

abbrev_fun_trans VectorType.exp in x [VectorType.Lawful X] : revFDeriv K by
  unfold revFDeriv
  fun_trans; to_ssa



@[data_synth]
theorem VectorType.Base.exp.arg_alphax.HasRevFDerivUpdate_simple_rule
    {X : Type} {n : outParam (Type)} {inst : outParam (IndexType n)} {R : outParam (Type)}
    {K : outParam (Type)} {inst_1 : outParam (RealScalar R)} {inst_2 : outParam (Scalar R K)}
    [self : VectorType.Base X n K] [inst_3 : VectorType.Lawful X] [VectorType.Dense X] :
    HasRevFDerivUpdate K
      (fun x : X => VectorType.exp x)
      (fun x =>
        let y := VectorType.exp x;
        (y, fun z dx =>
          let y' := VectorType.conj y;
          dx + VectorType.mul y' z)) := by
  constructor
  · fun_trans
  · fun_prop


@[data_synth]
theorem VectorType.Base.exp.arg_alphax.HasRevFDerivUpdate_comp_rule
    {X : Type} {n : outParam (Type)} {inst : outParam (IndexType n)} {R : outParam (Type)}
    {K : outParam (Type)} {inst_1 : outParam (RealScalar R)} {inst_2 : outParam (Scalar R K)}
    [self : VectorType.Base X n K] [inst_3 : VectorType.Lawful X] [VectorType.Dense X]
    {W : Type} [NormedAddCommGroup W] [AdjointSpace K W] [CompleteSpace W]
    (f : W → X) (f') (hf : HasRevFDerivUpdate K f f') :
    HasRevFDerivUpdate K
      (fun w => VectorType.exp (f w))
      (fun w =>
        let' (x,df') := f' w
        let y := VectorType.exp x
        (y, fun z dw =>
          let y' := VectorType.conj y;
          df' (VectorType.mul y' z) dw)) := by
  have ⟨hf',_⟩ := hf
  constructor
  · fun_trans [hf']
  · fun_prop
