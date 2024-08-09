import SciLean.Analysis.SpecialFunctions.Inner
import SciLean.Meta.GenerateFunProp

namespace SciLean

variable
  {R} [RealScalar R]
  {X} [NormedAddCommGroup X] [NormedSpace R X]
  {U} [NormedAddCommGroup U] [AdjointSpace R U] [CompleteSpace U]

def_fun_prop with_transitive : Differentiable R (fun u : U => ‖u‖₂²[R]) by
  unfold Norm2.norm2; fun_prop [Norm2.norm2]


@[fun_trans]
theorem Norm2.norm2.arg_a0.fderiv_rule :
    fderiv R (fun x : U => ‖x‖₂²[R])
    =
    fun x => fun dx =>L[R] 2 * ⟪dx,x⟫[R] := by
  ext x dx
  fun_trans [Norm2.norm2]
  rw[← AdjointSpace.conj_symm]
  simp; ring


@[fun_trans]
theorem Norm2.norm2.arg_a0.fwdFDeriv_rule :
    fwdFDeriv R (fun x : U => ‖x‖₂²[R])
    =
    fun x dx => (‖x‖₂²[R], 2 *⟪dx,x⟫[R]) := by
  unfold fwdFDeriv
  fun_trans


@[fun_trans]
theorem Norm2.norm2.arg_a0.revFDeriv_rule :
    revFDeriv R (fun x : U => ‖x‖₂²[R])
    =
    fun x => (‖x‖₂²[R], fun dr => (2 * dr)•x) := by
  unfold revFDeriv
  fun_trans [smul_smul]
