import SciLean.Data.VectorType.Operations.ToVec
import SciLean.Analysis.SpecialFunctions.StarRingEnd

namespace SciLean


section Simps

variable
  {R K} {_ : RealScalar R} {_ : Scalar R K}
  {n} {_ : IndexType n}
  {X} [VectorType.Base X n K]

@[simp,simp_core]
theorem VectorType.dot_zero_right (x : X) : VectorType.dot x 0 = 0 := by simp[vector_to_spec]

@[simp,simp_core]
theorem VectorType.dot_zero_left (x : X) : VectorType.dot 0 x = 0 := by simp[vector_to_spec]

end Simps


def_fun_prop VectorType.Base.dot in y [VectorType.Lawful X] : IsContinuousLinearMap K by
  simp[vector_to_spec]
  fun_prop

def_fun_prop VectorType.Base.dot in y
    add_suffix _real [ScalarSMul R K] [ScalarInner R K] [VectorType.Lawful X] [VectorType.RealOp X] : IsContinuousLinearMap R by
  simp[vector_to_spec]
  fun_prop


def_fun_prop VectorType.Base.dot in x [ScalarSMul R K] [ScalarInner R K] [VectorType.Lawful X] [VectorType.RealOp X] : IsContinuousLinearMap R by
  simp[vector_to_spec]
  fun_prop

def_fun_prop VectorType.Base.dot in x y [VectorType.Lawful X] : Continuous by
  simp[vector_to_spec]
  fun_prop

def_fun_prop VectorType.Base.dot in x y [ScalarSMul R K] [ScalarInner R K] [VectorType.Lawful X] [VectorType.RealOp X] : Differentiable R by
  simp only [VectorType.dot_spec, PiLp.inner_apply, WithLp.equiv_symm_pi_apply, RCLike.inner_apply]
  fun_prop

abbrev_fun_trans VectorType.Base.dot in x y [ScalarSMul R K] [ScalarInner R K] [VectorType.Lawful X] [VectorType.RealOp X] : fderiv R by
  rw[fderiv_wrt_prod (by fun_prop)]
  autodiff

abbrev_fun_trans VectorType.Base.dot in x y [ScalarSMul R K] [ScalarInner R K] [VectorType.Lawful X] [VectorType.RealOp X] : fwdFDeriv R by
  rw[fwdFDeriv_wrt_prod (by fun_prop)]
  autodiff

open ComplexConjugate in
abbrev_fun_trans VectorType.Base.dot in x [ScalarSMul R K] [ScalarInner R K] [VectorType.Lawful X] [VectorType.RealOp X] : adjoint R by
  equals (fun c => (conj c)•y) =>
    funext c
    apply AdjointSpace.ext_inner_left R
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec, sum_pull,Inner.inner]
    simp[inner,AdjointSpace.toInner,ScalarInner.inner_eq_inner_re_im]
    sorry_proof -- this should be true, just missing some API involving complex multiplication

abbrev_fun_trans VectorType.Base.dot in y [ScalarSMul R K] [ScalarInner R K] [VectorType.Lawful X] [VectorType.RealOp X] : adjoint R by
  equals (fun c => c•x) =>
    funext c
    apply AdjointSpace.ext_inner_left R
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec, sum_pull,Inner.inner]
    simp[inner,AdjointSpace.toInner,ScalarInner.inner_eq_inner_re_im]
    sorry_proof -- this should be true, just missing some API involving complex multiplication

abbrev_fun_trans VectorType.Base.dot in x y [ScalarSMul R K] [ScalarInner R K] [VectorType.Lawful X] [VectorType.RealOp X] : revFDeriv R by
  rw[revFDeriv_wrt_prod (by fun_prop)]
  unfold revFDeriv
  autodiff


section HasRevFDerivUpdate

variable
  {R K} {_ : RealScalar R} {_ : Scalar R K}
  {n} {_ : IndexType n}
  {X} [VectorType.Base X n K] [VectorType.Lawful X] [ScalarSMul R K] [ScalarInner R K] [VectorType.RealOp X]
  {W} [NormedAddCommGroup W] [AdjointSpace R W] [CompleteSpace W]


open ComplexConjugate


@[data_synth]
theorem VectorType.Base.dot.arg_xy.HasRevFDerivUpdate_rule_simple :
  HasRevFDerivUpdate R
    (fun x : X×X => VectorType.Base.dot x.1 x.2)
    (fun xy : X×X =>
      let' (x,y) := xy
      (VectorType.Base.dot x y,
       fun dz dxy =>
         let' (dx,dy) := dxy
         (axpy (conj dz) y dx, axpy dz x dy))) := by
  constructor
  · intro (x,y)
    fun_trans
    funext dz (dx,dy)
    ext i <;> (simp[vector_to_spec]; ac_rfl)
  · fun_prop


@[data_synth]
theorem VectorType.Base.dot.arg_xy.HasRevFDerivUpdate_rule
  (f g : W → X) {f' g'} (hf : HasRevFDerivUpdate R f f') (hg : HasRevFDerivUpdate R g g') :
  HasRevFDerivUpdate R
    (fun w => VectorType.Base.dot (f w) (g w))
    (fun w  =>
      let' (x,df') := f' w
      let' (y,dg') := g' w
      (VectorType.Base.dot x y,
       fun dz dw =>
         dg' (dz•x) (df' (conj dz•y) dw))) := by
  have ⟨hf',_⟩ := hf
  have ⟨hg',_⟩ := hg
  constructor
  · fun_trans [hf',hg',add_assoc]
  · fun_prop


end HasRevFDerivUpdate
