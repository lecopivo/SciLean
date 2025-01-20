import SciLean.Data.VectorType.Operations.ToVec
import SciLean.Data.VectorType.Operations.FromVec
import SciLean.Analysis.SpecialFunctions.StarRingEnd
import SciLean.Data.VectorType.Operations.Scal
import SciLean.Lean.ToSSA

namespace SciLean


section Simps


-- def_fun_prop VectorType.scalAdd in x with_transitive [VectorType.Lawful X] : IsContinuousLinearMap K by
--   apply (IsContinuousLinearMap.injective_comp_iff VectorType.toVec (by fun_prop) (VectorType.Lawful.toVec_injective)).2
--   simp[vector_to_spec]
--   fun_prop

-- def_fun_prop VectorType.scalAdd in alpha with_transitive [VectorType.Lawful X] : IsContinuousLinearMap K by
--   apply (IsContinuousLinearMap.injective_comp_iff VectorType.toVec (by fun_prop) (VectorType.Lawful.toVec_injective)).2
--   simp[vector_to_spec]
--   fun_prop

theorem IsAffineMap.injective_comp_iff
  {R : Type*} [RCLike R]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace R Z]
  {f : X → Y} (g : Y → Z) (_hg : IsAffineMap R g) (_hg' : g.Injective)  :
  IsAffineMap R f ↔ IsAffineMap R (fun x => g (f x)) := sorry_proof

@[fun_trans]
theorem fderiv_affine_map
  {R : Type*} [RCLike R]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace R Y] [FiniteDimensional R Y]
  {f : X → Y} (_hf : IsAffineMap R f) :
  fderiv R f = fun _ => ContinuousLinearMap.mk' R (fun dx => (f dx - f 0)) sorry_proof := sorry_proof

section Simps

variable
  {X : Type u_1} {n : outParam (Type u_2)}
  {_ : outParam (IndexType n)} {R : outParam (Type u_3)} {K : outParam (Type u_4)}
  {_ : outParam (RealScalar R)} {_ : outParam (Scalar R K)} [self : VectorType.Base X n K]

@[simp, simp_core]
theorem VectorType.Base.scalAdd_zero_beta_x
    [VectorType.Lawful X] [VectorType.Dense X]
    (beta : K) (x : X) :
    VectorType.scalAdd 0 beta x = VectorType.const beta := by
  apply VectorType.Lawful.toVec_injective
  simp[vector_to_spec]

@[simp, simp_core]
theorem VectorType.Base.scalAdd_alpha_zero_x
    [VectorType.Lawful X]
    (alpha : K) (x : X) :
    VectorType.scalAdd alpha 0 x = VectorType.scal alpha x := by
  apply VectorType.Lawful.toVec_injective
  funext i
  simp[vector_to_spec]

@[simp, simp_core]
theorem VectorType.Base.scalAdd_alpha_beta_zero
    [VectorType.Lawful X] [VectorType.Dense X]
    (alpha beta : K) :
    VectorType.scalAdd alpha beta (0:X) = VectorType.const beta := by
  apply VectorType.Lawful.toVec_injective
  simp[vector_to_spec]

end Simps

def_fun_prop VectorType.scalAdd in alpha with_transitive [VectorType.Lawful X] : IsAffineMap K by
  apply (IsAffineMap.injective_comp_iff VectorType.toVec (by fun_prop) (VectorType.Lawful.toVec_injective)).2
  simp[vector_to_spec]
  fun_prop

def_fun_prop VectorType.scalAdd in beta with_transitive [VectorType.Lawful X] : IsAffineMap K by
  apply (IsAffineMap.injective_comp_iff VectorType.toVec (by fun_prop) (VectorType.Lawful.toVec_injective)).2
  simp[vector_to_spec]
  fun_prop

def_fun_prop VectorType.scalAdd in x with_transitive [VectorType.Lawful X] : IsAffineMap K by
  apply (IsAffineMap.injective_comp_iff VectorType.toVec (by fun_prop) (VectorType.Lawful.toVec_injective)).2
  simp[vector_to_spec]
  fun_prop

def_fun_prop VectorType.scalAdd in alpha beta x with_transitive [VectorType.Lawful X] : Differentiable K by
  apply (Differentiable.injective_comp_iff VectorType.toVec (by fun_prop) (VectorType.Lawful.toVec_injective)).2
  simp[vector_to_spec]
  fun_prop


abbrev_fun_trans VectorType.scalAdd in alpha beta x [VectorType.Lawful X] [VectorType.Dense X] : fderiv K by
  rw[fderiv_wrt_prod3]
  autodiff
  simp[vector_from_spec]

abbrev_fun_trans VectorType.scalAdd in alpha beta x [VectorType.Lawful X] : fwdFDeriv K by
  unfold fwdFDeriv
  autodiff


-- open ComplexConjugate in
-- abbrev_fun_trans VectorType.scalAdd in x [VectorType.Lawful X] : adjoint K by
--   equals (fun y => VectorType.scalAdd (conj alpha) y) =>
--     funext c
--     apply AdjointSpace.ext_inner_left K
--     intro z
--     rw[← adjoint_ex _ (by fun_prop)]
--     simp[vector_to_spec, sum_pull,Inner.inner]
--     congr; funext x; ring

-- open ComplexConjugate in
-- abbrev_fun_trans VectorType.scalAdd in alpha [VectorType.Lawful X] : adjoint K by
--   equals (fun y => VectorType.dot x y) =>
--     funext z
--     apply AdjointSpace.ext_inner_left K
--     intro c
--     rw[← adjoint_ex _ (by fun_prop)]
--     simp[vector_to_spec, sum_pull,Inner.inner]
--     sorry_proof

-- abbrev_fun_trans VectorType.scalAdd in alpha x [VectorType.Lawful X] : revFDeriv K by
--   equals
--     (fun x : K×X =>
--       let' (alpha, x) := x
--       (VectorType.scalAdd alpha x,
--       fun y =>
--         (VectorType.dot x y,
--          VectorType.scalAdd ((starRingEnd K) alpha) y))) =>
--   unfold revFDeriv
--   fun_trans


-- @[data_synth]
-- theorem VectorType.Base.scalAdd.arg_alphax.HasRevFDerivUpdate_rule
--     {X : Type} {n : outParam (Type)} {inst : outParam (IndexType n)} {R : outParam (Type)}
--     {K : outParam (Type)} {inst_1 : outParam (RealScalAddar R)} {inst_2 : outParam (ScalAddar R K)}
--     [self : VectorType.Base X n K] [inst_3 : VectorType.Lawful X] :
--     HasRevFDerivUpdate K
--       (fun alphax : K×X => VectorType.scalAdd alphax.1 alphax.2)
--       (fun x : K×X =>
--         let' (alpha, x) := x
--         (VectorType.scalAdd alpha x,
--         fun y dalphax  =>
--           let' (dalpha,dx) := dalphax
--           (dalpha + VectorType.dot x y,
--            VectorType.axpy ((starRingEnd K) alpha) y dx))) := by
--   constructor
--   · fun_trans
--     intros a y; funext dy (da, dx)
--     simp
--     apply VectorType.Lawful.toVec_injective
--     simp[vector_to_spec,add_comm]
--   · fun_prop
