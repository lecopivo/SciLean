import SciLean.Data.VectorType.Operations.Scal

namespace SciLean


section Simps

variable
  {R K} {_ : RealScalar R} {_ : Scalar R K}
  {n} {_ : IndexType n}
  {X} [VectorType.Base X n K] [VectorType.Lawful X]

@[simp,simp_core]
theorem VectorType.mul_zero_right (x : X) : VectorType.mul x 0 = 0 := by
  apply VectorType.toVec_injective; simp[vector_to_spec]

@[simp,simp_core]
theorem VectorType.mul_zero_left (x : X) : VectorType.mul 0 x = 0 := by
  apply VectorType.toVec_injective; simp[vector_to_spec]

end Simps


def_fun_prop VectorType.Base.mul in x [VectorType.Lawful X] : IsContinuousLinearMap K by
  apply (IsContinuousLinearMap.injective_comp_iff VectorType.toVec (by fun_prop) (VectorType.Lawful.toVec_injective)).2
  simp[vector_to_spec]
  fun_prop

def_fun_prop VectorType.Base.mul in y [VectorType.Lawful X] : IsContinuousLinearMap K by
  apply (IsContinuousLinearMap.injective_comp_iff VectorType.toVec (by fun_prop) (VectorType.Lawful.toVec_injective)).2
  simp[vector_to_spec]
  fun_prop

def_fun_prop VectorType.Base.mul in x y [VectorType.Lawful X] : Differentiable K by
  apply (Differentiable.injective_comp_iff VectorType.toVec (by fun_prop) (VectorType.Lawful.toVec_injective)).2
  simp[vector_to_spec]
  fun_prop

abbrev_fun_trans VectorType.Base.mul in x y [VectorType.Lawful X] : fderiv K by
  rw[fderiv_wrt_prod (by fun_prop)]
  autodiff

abbrev_fun_trans VectorType.Base.mul in x y [VectorType.Lawful X] : fwdFDeriv K by
  rw[fwdFDeriv_wrt_prod (by fun_prop)]
  autodiff

abbrev_fun_trans VectorType.Base.mul in x [VectorType.Lawful X] : adjoint K by
  equals (fun z => VectorType.mul (VectorType.conj y) z) =>
    funext x
    apply AdjointSpace.ext_inner_left K
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec, sum_pull,Inner.inner]
    ac_rfl

abbrev_fun_trans VectorType.Base.mul in y [VectorType.Lawful X] : adjoint K by
  equals (fun z => VectorType.mul (VectorType.conj x) z) =>
    funext y
    apply AdjointSpace.ext_inner_left K
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec, sum_pull,Inner.inner]
    ac_rfl

abbrev_fun_trans VectorType.Base.mul in x y [VectorType.Lawful X] : revFDeriv K by
  rw[revFDeriv_wrt_prod (by fun_prop)]
  unfold revFDeriv
  autodiff


section HasRevFDerivUpdate

variable
  {R K} {_ : RealScalar R} {_ : Scalar R K}
  {n} {_ : IndexType n}
  {X} [VectorType.Base X n K] [VectorType.Lawful X]
  {W} [NormedAddCommGroup W] [AdjointSpace K W] [CompleteSpace W]

@[data_synth]
theorem VectorType.Base.mul.arg_xy.HasRevFDerivUpdate_rule_simple :
  HasRevFDerivUpdate K
    (fun x : X×X => VectorType.Base.mul x.1 x.2)
    (fun xy : X×X =>
      let' (x,y) := xy
      (VectorType.Base.mul x y,
       fun dz dxy =>
         let' (dx,dy) := dxy
         (dx + mul (conj y) dz, dy + mul (conj x) dz))) := by
  constructor
  · intro (x,y)
    fun_trans
    funext dz (dx,dy)
    ext i <;> (simp[vector_to_spec])
  · fun_prop


@[data_synth]
theorem VectorType.Base.mul.arg_xy.HasRevFDerivUpdate_rule
  (f g : W → X) {f' g'} (hf : HasRevFDerivUpdate K f f') (hg : HasRevFDerivUpdate K g g') :
  HasRevFDerivUpdate K
    (fun w => VectorType.Base.mul (f w) (g w))
    (fun w  =>
      let' (x,df') := f' w
      let' (y,dg') := g' w
      (VectorType.Base.mul x y,
       fun dz dw =>
         dg' (mul (conj x) dz) (df' (mul (conj y) dz) dw))) := by
  have ⟨hf',_⟩ := hf
  have ⟨hg',_⟩ := hg
  constructor
  · fun_trans [hf',hg',add_assoc]
  · fun_prop


end HasRevFDerivUpdate
