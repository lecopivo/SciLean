import SciLean.Data.VectorType.Operations.ToVec
import SciLean.Data.VectorType.Optimize
import SciLean.Analysis.SpecialFunctions.StarRingEnd

namespace SciLean

open VectorType
section Simps

variable
  {R K} {_ : RealScalar R} {_ : Scalar R K}
  {n} {_ : IndexType n}
  {X} [VectorType.Base X n K]

theorem hoho [Dense X] (x : X) : x = fromVec (toVec x) := sorry_proof

@[vector_from_spec]
theorem fromVec_const [Lawful X] [Dense X] (k : K) :
    fromVec (X:=X) (fun _ : n => k) = const k := by
  ext i; simp [vector_to_spec]

@[vector_from_spec]
theorem toVec_sum [Lawful X] {I} [Fintype I] (A : Finset I) (f : I → X) :
    toVec (A.sum f) = fun j => A.sum (fun i => toVec (f i) j) := sorry_proof

-- linearity
def_fun_prop VectorType.sum in x with_transitive [VectorType.Lawful X] : IsContinuousLinearMap K by
  simp[vector_to_spec]
  fun_prop

#generate_linear_map_simps VectorType.Base.sum.arg_x.IsLinearMap_rule

-- fderiv
abbrev_fun_trans VectorType.sum in x [VectorType.Lawful X] : fderiv K by autodiff
abbrev_data_synth VectorType.sum in x [VectorType.Lawful X] (x₀) : (HasFDerivAt (𝕜:=K) · · x₀) by
  exact hasFDerivAt_from_isContinuousLinearMap

-- forward AD
abbrev_fun_trans VectorType.sum in x [VectorType.Lawful X] : fwdFDeriv K by autodiff

-- adjoint
open ComplexConjugate Classical in

open Classical in
abbrev_fun_trans VectorType.sum in x [Lawful X] [Dense X] : adjoint K by
  enter[y]; simp[vector_to_spec]
  fun_trans
  rw[hoho (Finset.sum _ _)]; simp [vector_from_spec, vector_to_spec]

open Classical in
abbrev_data_synth VectorType.sum in x [Lawful X] [Dense X] :
    HasAdjoint K by
  conv => enter[3]; assign (fun y => VectorType.const (X:=X) y)
  constructor
  case adjoint   => intros; simp[vector_to_spec,Finset.sum_mul]
  case is_linear => fun_prop

abbrev_data_synth VectorType.sum in x [Lawful X] [Dense X] :
    HasAdjointUpdate K by
  apply hasAdjointUpdate_from_hasAdjoint
  case adjoint => data_synth
  case simp => intros; simp [vector_optimize]; rfl


-- reverse AD
abbrev_fun_trans VectorType.sum in x [VectorType.Lawful X] [VectorType.Dense X] : revFDeriv K by
  unfold revFDeriv
  fun_trans

abbrev_data_synth VectorType.sum in x [VectorType.Lawful X] [VectorType.Dense X] :
    HasRevFDeriv K by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl

abbrev_data_synth VectorType.sum in x [VectorType.Lawful X] [VectorType.Dense X] :
    HasRevFDerivUpdate K by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl
