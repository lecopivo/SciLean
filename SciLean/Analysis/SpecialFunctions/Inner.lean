import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Analysis.Calculus.RevFDeriv

import SciLean.Core.Meta.GenerateFunProp
import SciLean.Core.Meta.GenerateFunTrans

namespace SciLean

variable
  {R} [RealScalar R]
  {X} [NormedAddCommGroup X] [NormedSpace R X]
  {U} [NormedAddCommGroup U] [AdjointSpace R U] [CompleteSpace U]


theorem Inner.inner.arg_a0a1.IsBoundedBilinearMap_rule :
    IsBoundedBilinearMap R (fun (x : U×U) => ⟪x.1,x.2⟫[R]) := sorry_proof


def_fun_prop with_transitive : Differentiable R (fun (x : U×U) => ⟪x.1,x.2⟫[R]) by
  fun_prop (disch:=apply Inner.inner.arg_a0a1.IsBoundedBilinearMap_rule)

-- abbrev_fun_trans (x : U×U) : fderiv R (fun x : U×U => ⟪x.1, x.2⟫[R]) x by
--   equals (fun dx =>L[R] ⟪x.1,dx.2⟫[R] + ⟪dx.1,x.2⟫[R]) => sorry_proof

@[fun_trans]
theorem _root_.Inner.inner.arg_a0a1.fderiv_rule :
  fderiv R (fun x : U×U => ⟪x.1, x.2⟫[R])
  =
  fun x => fun dx =>L[R]
    ⟪x.1,dx.2⟫[R] + ⟪dx.1,x.2⟫[R] := by sorry_proof

@[fun_trans]
theorem _root_.Inner.inner.arg_a0a1.fwdFDeriv_rule :
  fwdFDeriv R (fun x : U×U => ⟪x.1, x.2⟫[R])
  =
  fun x dx =>
    (⟪x.1,x.2⟫[R], ⟪x.1,dx.2⟫[R] + ⟪dx.1,x.2⟫[R]) := by unfold fwdFDeriv; fun_trans

@[fun_trans]
theorem _root_.Inner.inner.arg_a0a1.revFDeriv_rule :
  revFDeriv R (fun x : U×U => ⟪x.1, x.2⟫[R])
  =
  fun x =>
    (⟪x.1,x.2⟫[R], fun dr => (dr • x.2, dr • x.1)) := by unfold revFDeriv; fun_trans
