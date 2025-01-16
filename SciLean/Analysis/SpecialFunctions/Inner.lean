import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Analysis.Calculus.RevFDeriv

import SciLean.Meta.GenerateFunProp
-- import SciLean.Meta.GenerateFunTrans

namespace SciLean

set_option deprecated.oldSectionVars true

variable
  {R K : Type*} [RealScalar R] [Scalar R K] [ScalarSMul R K] [ScalarInner R K]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace R X] [NormedSpace K X]
  {U : Type*} [NormedAddCommGroup U] [AdjointSpace R U] [AdjointSpace K U] [CompleteSpace U]


theorem Inner.inner.arg_a0a1.IsBoundedBilinearMap_rule :
    IsBoundedBilinearMap R (fun (x : U×U) => ⟪x.1,x.2⟫[K]) := sorry_proof


def_fun_prop with_transitive : Differentiable R (fun (x : U×U) => ⟪x.1,x.2⟫[K]) by
  fun_prop (disch:=apply Inner.inner.arg_a0a1.IsBoundedBilinearMap_rule)

def_fun_prop with_transitive _real : Differentiable R (fun (x : U×U) => ⟪x.1,x.2⟫[R]) by
  fun_prop

-- abbrev_fun_trans (x : U×U) : fderiv R (fun x : U×U => ⟪x.1, x.2⟫[R]) x by
--   equals (fun dx =>L[R] ⟪x.1,dx.2⟫[R] + ⟪dx.1,x.2⟫[R]) => sorry_proof

@[fun_trans]
theorem _root_.Inner.inner.arg_a0a1.fderiv_rule :
  fderiv R (fun x : U×U => ⟪x.1, x.2⟫[K])
  =
  fun x => fun dx =>L[R]
    ⟪x.1,dx.2⟫[K] + ⟪dx.1,x.2⟫[K] := by sorry_proof

@[fun_trans]
theorem _root_.Inner.inner.arg_a0a1.fwdFDeriv_rule :
  fwdFDeriv R (fun x : U×U => ⟪x.1, x.2⟫[K])
  =
  fun x dx =>
    (⟪x.1,x.2⟫[K], ⟪x.1,dx.2⟫[K] + ⟪dx.1,x.2⟫[K]) := by unfold fwdFDeriv; fun_trans

open ComplexConjugate in
@[fun_trans]
theorem _root_.Inner.inner.arg_a0a1.revFDeriv_rule :
  revFDeriv R (fun x : U×U => ⟪x.1, x.2⟫[K])
  =
  fun x =>
    (⟪x.1,x.2⟫[K], fun dr => (conj dr • x.2, dr • x.1)) := by unfold revFDeriv; fun_trans
