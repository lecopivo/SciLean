import SciLean.Data.VectorType.Operations.ToVec
import SciLean.Analysis.SpecialFunctions.StarRingEnd

namespace SciLean


section Simps

variable
  {R K} {_ : RealScalar R} {_ : Scalar R K}
  {n} {_ : IndexType n}
  {X} [VectorType.Base X n K]

def_fun_prop VectorType.sum in x with_transitive [VectorType.Lawful X] : IsContinuousLinearMap K by
  simp[vector_to_spec]
  fun_prop


abbrev_fun_trans VectorType.sum in x [VectorType.Lawful X] : fderiv K by autodiff
abbrev_fun_trans VectorType.sum in x [VectorType.Lawful X] : fwdFDeriv K by autodiff

open ComplexConjugate in
abbrev_fun_trans VectorType.sum in x [VectorType.Lawful X] [VectorType.Dense X] : adjoint K by
  equals (fun y => VectorType.const y) =>
    funext c
    apply AdjointSpace.ext_inner_left K
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec]
    sorry_proof

abbrev_fun_trans VectorType.sum in x [VectorType.Lawful X] [VectorType.Dense X] : revFDeriv K by
  unfold revFDeriv
  fun_trans


@[data_synth]
theorem VectorType.Base.sum.arg_x.HasRevFDerivUpdate_rule_simple
    {X : Type} {n : outParam (Type)} {inst : outParam (IndexType n)} {R : outParam (Type)}
    {K : outParam (Type)} {inst_1 : outParam (RealScalar R)} {inst_2 : outParam (Scalar R K)}
    [self : VectorType.Base X n K] [inst_3 : VectorType.Lawful X] [VectorType.Dense X] :
    HasRevFDerivUpdate K
      (fun x : X => VectorType.sum x)
      (fun x : X =>
        (VectorType.sum x,
         fun dy dx =>
           VectorType.scalAdd 1 dy dx)) := by
  constructor
  · simp;
    intros x; funext dy dx; fun_trans
    ext i; simp [vector_to_spec]
  · fun_prop


@[data_synth]
theorem VectorType.Base.sum.arg_x.HasRevFDerivUpdate_rule
    {X : Type} {n : outParam (Type)} {inst : outParam (IndexType n)} {R : outParam (Type)}
    {K : outParam (Type)} {inst_1 : outParam (RealScalar R)} {inst_2 : outParam (Scalar R K)}
    [self : VectorType.Base X n K] [inst_3 : VectorType.Lawful X] [VectorType.Dense X]
    {W : Type} [NormedAddCommGroup W] [AdjointSpace K W] [CompleteSpace W]
    (f : W → X) (f') (hf : HasRevFDerivUpdate K f f') :
    HasRevFDerivUpdate K
      (fun w : W => VectorType.sum (f w))
      (fun w : W =>
        let' (x,df') := f' w
        (VectorType.sum x,
         fun dy dw =>
           df' (VectorType.const dy) dw)) := by
  have ⟨hf',_⟩ := hf
  constructor
  · simp[hf']
    intros x; funext dy dx; fun_trans
  · fun_prop
