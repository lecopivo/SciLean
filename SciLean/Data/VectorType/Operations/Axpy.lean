import SciLean.Data.VectorType.Operations.Scal
import SciLean.Lean.ToSSA

namespace SciLean

def_fun_prop VectorType.Base.axpy in alpha y [VectorType.Lawful X] : IsContinuousLinearMap K by
  apply (IsContinuousLinearMap.injective_comp_iff VectorType.toVec (by fun_prop) (VectorType.Lawful.toVec_injective)).2
  simp[vector_to_spec]
  fun_prop

def_fun_prop VectorType.Base.axpy in x y [VectorType.Lawful X] : IsContinuousLinearMap K by
  apply (IsContinuousLinearMap.injective_comp_iff VectorType.toVec (by fun_prop) (VectorType.Lawful.toVec_injective)).2
  simp[vector_to_spec]
  fun_prop

def_fun_prop VectorType.Base.axpy in alpha [VectorType.Lawful X] : IsAffineMap K by
  sorry_proof

def_fun_prop VectorType.Base.axpy in alpha x y [VectorType.Lawful X] : Differentiable K by
  apply (Differentiable.injective_comp_iff VectorType.toVec (by fun_prop) (VectorType.Lawful.toVec_injective)).2
  simp[vector_to_spec]
  fun_prop

abbrev_fun_trans VectorType.Base.axpy in alpha [VectorType.Lawful X] : fderiv K by
  equals (fun _ => fun da =>L[K] VectorType.scal da x) =>
    funext a; ext : 1
    apply VectorType.Lawful.toVec_injective; funext i
    rw[toVec_fderiv (hf:=by fun_prop)]; simp [vector_to_spec]

abbrev_fun_trans VectorType.Base.axpy in alpha x y [VectorType.Lawful X] : fderiv K by
  rw[fderiv_wrt_prod (K:=K) (f:=fun a (xy : X×X) => VectorType.axpy a xy.1 xy.2) (by fun_prop)]
  autodiff

abbrev_fun_trans VectorType.Base.axpy in alpha x y [VectorType.Lawful X] : fwdFDeriv K by
  unfold fwdFDeriv
  autodiff

open ComplexConjugate in
abbrev_fun_trans VectorType.Base.axpy in x y [VectorType.Lawful X] : adjoint K by
  equals (fun z => (VectorType.scal (conj alpha) z, z)) =>
    funext z
    apply AdjointSpace.ext_inner_left K
    intro c
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec, sum_pull,Inner.inner, Finset.sum_add_distrib, add_mul]
    ac_rfl

abbrev_fun_trans VectorType.Base.axpy in alpha y [VectorType.Lawful X] : adjoint K by
  equals (fun z => (VectorType.dot x z, z)) =>
    funext z
    apply AdjointSpace.ext_inner_left K
    intro c
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec, sum_pull,Inner.inner, Finset.sum_add_distrib, add_mul, Finset.mul_sum]
    ac_rfl

abbrev_fun_trans VectorType.Base.axpy in alpha x y [VectorType.Lawful X] : revFDeriv K by
  unfold revFDeriv
  fun_trans
  -- to_ssa  -- I don't like the current result
