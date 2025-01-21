import SciLean.Data.VectorType.Operations.ToVec
import SciLean.Analysis.SpecialFunctions.StarRingEnd

namespace SciLean


section Simps

variable
  {R K} {_ : RealScalar R} {_ : Scalar R K}
  {n} {_ : IndexType n}
  {X} [VectorType.Base X n K] [VectorType.Lawful X]

@[simp, simp_core]
theorem VectorType.scal_one (x : X) :
    VectorType.scal 1 x = x := by ext i; simp[vector_to_spec]

@[simp, simp_core]
theorem VectorType.scal_zero (x : X) :
    VectorType.scal 0 x = 0 := by ext i; simp[vector_to_spec]

@[simp, simp_core]
theorem VectorType.scal_zero' (a : K) :
    VectorType.scal a (0:X) = 0 := by ext i; simp[vector_to_spec]

end Simps

set_option linter.unusedVariables false in
theorem IsContinuousLinearMap.injective_comp_iff
  {R : Type*} [RCLike R]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace R Z]
  {f : X → Y} (g : Y → Z) (hg : IsContinuousLinearMap R g) (hg' : g.Injective)  :
  IsContinuousLinearMap R f ↔ IsContinuousLinearMap R (fun x => g (f x)) := sorry_proof

set_option linter.unusedVariables false in
theorem Differentiable.injective_comp_iff
  {R : Type*} [RCLike R]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace R Z]
  {f : X → Y} (g : Y → Z) (hg : Differentiable R g) (hg' : g.Injective)  :
  Differentiable R f ↔ Differentiable R (fun x => g (f x)) := sorry_proof


def_fun_prop VectorType.scal in x with_transitive [VectorType.Lawful X] : IsContinuousLinearMap K by
  apply (IsContinuousLinearMap.injective_comp_iff VectorType.toVec (by fun_prop) (VectorType.Lawful.toVec_injective)).2
  simp[vector_to_spec]
  fun_prop

def_fun_prop VectorType.scal in alpha with_transitive [VectorType.Lawful X] : IsContinuousLinearMap K by
  apply (IsContinuousLinearMap.injective_comp_iff VectorType.toVec (by fun_prop) (VectorType.Lawful.toVec_injective)).2
  simp[vector_to_spec]
  fun_prop

def_fun_prop VectorType.scal in alpha x with_transitive [VectorType.Lawful X] : Differentiable K by
  apply (Differentiable.injective_comp_iff VectorType.toVec (by fun_prop) (VectorType.Lawful.toVec_injective)).2
  simp[vector_to_spec]
  fun_prop


abbrev_fun_trans VectorType.scal in alpha x [VectorType.Lawful X] : fderiv K by
  rw[fderiv_wrt_prod]
  autodiff

abbrev_fun_trans VectorType.scal in alpha x [VectorType.Lawful X] : fwdFDeriv K by
  rw[fwdFDeriv_wrt_prod]
  autodiff

open ComplexConjugate in
abbrev_fun_trans VectorType.scal in x [VectorType.Lawful X] : adjoint K by
  equals (fun y => VectorType.scal (conj alpha) y) =>
    funext c
    apply AdjointSpace.ext_inner_left K
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec, sum_pull,Inner.inner]
    congr; funext x; ring

open ComplexConjugate in
abbrev_fun_trans VectorType.scal in alpha [VectorType.Lawful X] : adjoint K by
  equals (fun y => VectorType.dot x y) =>
    funext z
    apply AdjointSpace.ext_inner_left K
    intro c
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec, sum_pull,Inner.inner]
    sorry_proof

abbrev_fun_trans VectorType.scal in alpha x [VectorType.Lawful X] : revFDeriv K by
  equals
    (fun x : K×X =>
      let' (alpha, x) := x
      (VectorType.scal alpha x,
      fun y =>
        (VectorType.dot x y,
         VectorType.scal ((starRingEnd K) alpha) y))) =>
  unfold revFDeriv
  fun_trans


@[data_synth]
theorem VectorType.Base.scal.arg_alphax.HasRevFDerivUpdate_rule
    {X : Type} {n : outParam (Type)} {inst : outParam (IndexType n)} {R : outParam (Type)}
    {K : outParam (Type)} {inst_1 : outParam (RealScalar R)} {inst_2 : outParam (Scalar R K)}
    [self : VectorType.Base X n K] [inst_3 : VectorType.Lawful X] :
    HasRevFDerivUpdate K
      (fun alphax : K×X => VectorType.scal alphax.1 alphax.2)
      (fun x : K×X =>
        let' (alpha, x) := x
        (VectorType.scal alpha x,
        fun y dalphax  =>
          let' (dalpha,dx) := dalphax
          (dalpha + VectorType.dot x y,
           VectorType.axpy ((starRingEnd K) alpha) y dx))) := by
  constructor
  · fun_trans
    intros a y; funext dy (da, dx)
    simp
    apply VectorType.Lawful.toVec_injective
    simp[vector_to_spec,add_comm]
  · fun_prop
