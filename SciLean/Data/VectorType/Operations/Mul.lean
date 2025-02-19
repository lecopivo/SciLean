import SciLean.Data.VectorType.Operations.Scal
import SciLean.Data.VectorType.Operations.ToVec
import SciLean.Data.VectorType.Operations.FromVec

namespace SciLean

open VectorType
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

-- linear, differentiable
def_fun_prop mul in x [InjectiveGetElem X n] : IsContinuousLinearMap K by
  apply (IsContinuousLinearMap.injective_comp_iff (fun x (i : n) => (getElem x i True.intro)) (by fun_prop) (getElem_injective)).2
  simp[vector_to_spec]
  fun_prop

def_fun_prop mul in y [InjectiveGetElem X n] : IsContinuousLinearMap K by
  apply (IsContinuousLinearMap.injective_comp_iff (fun x (i : n) => (getElem x i True.intro)) (by fun_prop) (getElem_injective)).2
  simp[vector_to_spec]
  fun_prop

def_fun_prop mul in x y [InjectiveGetElem X n] : Differentiable K by
  apply (Differentiable.injective_comp_iff (fun x (i : n) => (getElem x i True.intro)) (by fun_prop) (getElem_injective)).2
  simp[vector_to_spec]
  fun_prop

-- fderiv
abbrev_fun_trans mul in x y [InjectiveGetElem X n] : fderiv K by
  -- conv => enter [2,xy]; rw[← fromVec_toVec (mul _ _)]; simp[vector_to_spec]
  -- fun_trans
  -- simp[vector_from_spec]
  rw[fderiv_wrt_prod (by fun_prop)]
  autodiff

abbrev_data_synth mul in x y [InjectiveGetElem X n] (x₀) : (HasFDerivAt (𝕜:=K) · · x₀) by
  apply hasFDerivAt_from_fderiv
  case deriv => conv => rhs; autodiff
  case diff => dsimp[autoParam]; fun_prop

-- forward AD
abbrev_fun_trans mul in x y [InjectiveGetElem X n] : fwdFDeriv K by
  -- conv => enter [2,xy]; rw[← fromVec_toVec (mul _ _)]; simp[vector_to_spec]
  -- fun_trans
  -- simp[vector_from_spec]; to_ssa; to_ssa; lsimp
  rw[fwdFDeriv_wrt_prod (by fun_prop)]
  autodiff

-- adjoint
abbrev_fun_trans mul in x [InjectiveGetElem X n] : adjoint K by
  -- conv => enter [2,xy]; rw[← fromVec_toVec (mul _ _)]; simp[vector_to_spec]; eta_expand; simp
  -- fun_trans
  equals (fun z => mul (conj y) z) =>
    funext x
    apply AdjointSpace.ext_inner_left K
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec, sum_pull,Inner.inner]
    ac_rfl

abbrev_fun_trans mul in y [InjectiveGetElem X n] : adjoint K by
  equals (fun z => mul (conj x) z) =>
    funext y
    apply AdjointSpace.ext_inner_left K
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec, sum_pull,Inner.inner]
    ac_rfl

abbrev_data_synth mul in x [InjectiveGetElem X n] : HasAdjoint K by
  conv => enter[3]; assign (fun z => mul (conj y) z)
  constructor
  case adjoint => intros; simp[vector_to_spec]; ac_rfl
  case is_linear => fun_prop

abbrev_data_synth mul in x [InjectiveGetElem X n] : HasAdjointUpdate K by
  apply hasAdjointUpdate_from_hasAdjoint
  case adjoint => data_synth
  case simp => intros; conv => rhs; simp[vector_optimize]; rfl

abbrev_data_synth mul in y [InjectiveGetElem X n] : HasAdjoint K by
  conv => enter[3]; assign (fun z => mul (conj x) z)
  constructor
  case adjoint => intros; simp[vector_to_spec]; ac_rfl
  case is_linear => fun_prop

abbrev_data_synth mul in y [InjectiveGetElem X n] : HasAdjointUpdate K by
  apply hasAdjointUpdate_from_hasAdjoint
  case adjoint => data_synth
  case simp => intros; conv => rhs; simp[vector_optimize]; rfl


-- reverse AD
abbrev_fun_trans mul in x y [InjectiveGetElem X n] : revFDeriv K by
  rw[revFDeriv_wrt_prod (by fun_prop)]
  unfold revFDeriv
  autodiff

abbrev_data_synth mul in x y [InjectiveGetElem X n]
    -- arg_subsets [x] [y]
    : HasRevFDeriv K by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intros; dsimp; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => conv => rhs; simp[vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth mul in x y [InjectiveGetElem X n]
    -- arg_subsets [x] [y]
    : HasRevFDerivUpdate K by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intros; dsimp; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => conv => rhs; simp[vector_optimize]; to_ssa; to_ssa; lsimp


-- abbrev_data_synth_args mul in [x] [y] from [x,y] [InjectiveGetElem X n] : HasRevFDeriv K by
--   lsimp

-- argument subset - todo: automate this!
abbrev_data_synth mul in x [InjectiveGetElem X n] : HasRevFDeriv K by
  apply hasRevFDeriv_from_hasRevFDeriv
  case deriv =>
    apply HasRevFDeriv.comp_rule
              (g:=fun x => (x,y))
              (f:=fun xy : X×X => mul xy.1 xy.2)
              (hg:=by data_synth)
              (hf:=by data_synth)
  case simp => conv => rhs; lsimp

-- argument subset - todo: automate this!
abbrev_data_synth mul in y [InjectiveGetElem X n] : HasRevFDeriv K by
  apply hasRevFDeriv_from_hasRevFDeriv
  case deriv =>
    apply HasRevFDeriv.comp_rule
              (g:=fun y => (x,y))
              (f:=fun xy : X×X => mul xy.1 xy.2)
              (hg:=by data_synth)
              (hf:=by data_synth)
  case simp => conv => rhs; lsimp


-- abbrev_data_synth_args mul in [x] [y] from [x,y] [InjectiveGetElem X n] : HasRevFDerivUpdate K by
--   lsimp

-- argument subset - todo: automate this!
abbrev_data_synth mul in x [InjectiveGetElem X n] : HasRevFDerivUpdate K by
  apply hasRevFDerivUpdate_from_hasRevFDerivUpdate
  case deriv =>
    apply HasRevFDerivUpdate.comp_rule
              (g:=fun x => (x,y))
              (f:=fun xy : X×X => mul xy.1 xy.2)
              (hg:=by data_synth)
              (hf:=by data_synth)
  case simp => conv => rhs; lsimp

-- argument subset - todo: automate this!
abbrev_data_synth mul in y [InjectiveGetElem X n] : HasRevFDerivUpdate K by
  apply hasRevFDerivUpdate_from_hasRevFDerivUpdate
  case deriv =>
    apply HasRevFDerivUpdate.comp_rule
              (g:=fun y => (x,y))
              (f:=fun xy : X×X => mul xy.1 xy.2)
              (hg:=by data_synth)
              (hf:=by data_synth)
  case simp => conv => rhs; lsimp
