import SciLean.Data.VectorType.Operations.Exp
import SciLean.Data.VectorType.Operations.Sum
import SciLean.Data.VectorType.Operations.Mul
import SciLean.Analysis.SpecialFunctions.Log

namespace SciLean

section Simps

variable
  {X : Type*} {n : Type u} {R :  Type*}
  {_ : RealScalar R} {_ : IndexType n} [VectorType.Base X n R] [VectorType.Dense X]

theorem VectorType.logsumexp_spec (x : X) :
  VectorType.logsumexp x
  =
  if 0 < size n then
    Scalar.log (sum (exp x))
  else
    0 := sorry_proof

end Simps

def_fun_prop VectorType.logsumexp in x with_transitive [VectorType.Lawful X] : Differentiable R by
  -- simp only [VectorType.logsumexp_spec]
  -- have h : ∀ (w : X), VectorType.sum (VectorType.exp w) ≠ 0 := sorry_proof
  -- fun_prop (disch:=sorry_proof)
  sorry_proof

abbrev_fun_trans VectorType.logsumexp in x [VectorType.Lawful X] : fderiv R by
  equals (fun x => fun dx =>L[R]
           let x' := VectorType.softmax x
           ⟪dx, x'⟫[R]) =>
    sorry_proof

abbrev_fun_trans VectorType.logsumexp in x [VectorType.Lawful X] : fwdFDeriv R by
  unfold fwdFDeriv
  fun_trans; to_ssa

abbrev_fun_trans VectorType.logsumexp in x [VectorType.Lawful X] : revFDeriv R by
  unfold revFDeriv
  fun_trans; to_ssa


@[data_synth]
theorem VectorType.logsumexp.arg_alphax.HasRevFDerivUpdate_simple_rule
    {X : Type} {n : outParam (Type)} {inst : outParam (IndexType n)} {R : outParam (Type)}
    {inst_1 : outParam (RealScalar R)}
    [self : VectorType.Base X n R] [inst_3 : VectorType.Lawful X] [VectorType.Dense X] :
    HasRevFDerivUpdate R
      (fun x : X => VectorType.logsumexp x)
      (fun x =>
        let a := VectorType.logsumexp x;
        (a, fun z dx =>
          let a := VectorType.softmax x;
          VectorType.axpy z a dx)) := by
  constructor
  · fun_trans; intro x; funext dy dx
    apply toVec_injective; funext i
    simp[vector_to_spec]; ac_rfl
  · fun_prop


@[data_synth]
theorem VectorType.Base.logsumexp.arg_alphax.HasRevFDerivUpdate_comp_rule
    {X : Type} {n : outParam (Type)} {inst : outParam (IndexType n)} {R : outParam (Type)}
    {inst_1 : outParam (RealScalar R)}
    [self : VectorType.Base X n R] [inst_3 : VectorType.Lawful X] [VectorType.Dense X]
    {W : Type} [NormedAddCommGroup W] [AdjointSpace R W] [CompleteSpace W]
    (f : W → X) (f') (hf : HasRevFDerivUpdate R f f') :
    HasRevFDerivUpdate R
      (fun w => VectorType.logsumexp (f w))
      (fun w =>
        let' (x,df') := f' w
        let y := VectorType.logsumexp x
        (y, fun dz dw =>
          let y' := VectorType.softmax x;
          df' (dz•y') dw)) := by
  have ⟨hf',_⟩ := hf
  constructor
  · fun_trans [hf']
  · fun_prop
