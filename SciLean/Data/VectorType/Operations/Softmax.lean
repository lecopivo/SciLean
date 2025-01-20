import SciLean.Data.VectorType.Operations.Exp
import SciLean.Data.VectorType.Operations.Sum
import SciLean.Data.VectorType.Operations.Mul
import SciLean.Data.VectorType.Operations.Axpy
import SciLean.Analysis.SpecialFunctions.Log

namespace SciLean

section Simps

variable
  {X : Type*} {n : Type u} {R :  Type*}
  {_ : RealScalar R} {_ : IndexType n} [VectorType.Base X n R] [VectorType.Dense X]

theorem VectorType.softmax_spec (x : X) :
  VectorType.softmax x
  =
  let x' := exp x
  let w := sum x'
  w⁻¹ • x' := sorry_proof

end Simps

def_fun_prop VectorType.softmax in x with_transitive [VectorType.Lawful X] : Differentiable R by
  -- simp only [VectorType.softmax_spec]
  -- have h : ∀ (w : X), VectorType.sum (VectorType.exp w) ≠ 0 := sorry_proof
  -- fun_prop (disch:=sorry_proof)
  sorry_proof

abbrev_fun_trans VectorType.softmax in x [VectorType.Lawful X] : fderiv R by
  equals (fun x => fun dx =>L[R]
           let x' := VectorType.softmax x
           let s := - ⟪dx, x'⟫[R]
           VectorType.axpy s x' (VectorType.mul x' dx)) =>
    sorry_proof

abbrev_fun_trans VectorType.softmax in x [VectorType.Lawful X] : fwdFDeriv R by
  unfold fwdFDeriv
  fun_trans; to_ssa

abbrev_fun_trans VectorType.softmax in x [VectorType.Lawful X] : revFDeriv R by
  unfold revFDeriv
  fun_trans; to_ssa


@[data_synth]
theorem VectorType.softmax.arg_alphax.HasRevFDerivUpdate_simple_rule
    {X : Type} {n : outParam (Type)} {inst : outParam (IndexType n)} {R : outParam (Type)}
    {inst_1 : outParam (RealScalar R)}
    [self : VectorType.Base X n R] [inst_3 : VectorType.Lawful X] [VectorType.Dense X] :
    HasRevFDerivUpdate R
      (fun x : X => VectorType.softmax x)
      (fun x =>
        let a := VectorType.softmax x;
        (a, fun z dx =>
          let a_1 := VectorType.dot a z;
          let dx := VectorType.axpy (-a_1) a dx
          let a := VectorType.conj a;
          let a := VectorType.mul a z;
          dx + a)) := by
  constructor
  · fun_trans; intro x; funext dy dx
    apply toVec_injective; funext i
    simp[vector_to_spec];
    ac_rfl
  · fun_prop

@[data_synth]
theorem VectorType.softmax.arg_alphax.HasRevFDerivUpdate_comp_rule
    {X : Type} {n : outParam (Type)} {inst : outParam (IndexType n)} {R : outParam (Type)}
    {inst_1 : outParam (RealScalar R)}
    [self : VectorType.Base X n R] [inst_3 : VectorType.Lawful X] [VectorType.Dense X]
    {W : Type} [NormedAddCommGroup W] [AdjointSpace R W] [CompleteSpace W]
    (f : W → X) (f') (hf : HasRevFDerivUpdate R f f') :
    HasRevFDerivUpdate R
      (fun w => VectorType.softmax (f w))
      (fun w =>
        let' (x,df') := f' w
        let y := VectorType.softmax x;
        (y, fun z dw =>
          let a_1 := VectorType.dot y z;
          let a_2 := a_1 • y;
          let a_3 := -a_2;
          let a := VectorType.conj y;
          let a := VectorType.mul a z;
          let dx := a_3 + a
          df' dx dw)) := by
  have ⟨hf',_⟩ := hf
  constructor
  · fun_trans [hf']
  · fun_prop
