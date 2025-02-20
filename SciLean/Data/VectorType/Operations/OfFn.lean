import SciLean.Data.VectorType.Operations.ToVec

namespace SciLean

/-! Properties of `OfFn.ofFn` for types satisfying `VectorType`

TODO: There should be a dedicated class stating that vector space structure is compatible with
      array structure and all these theorems should be generalized to that.
-/

variable {X : Type u_1} {n : outParam (Type u_2)}
  {x : outParam (IndexType n)} {R : outParam (Type u_3)} {K : outParam (Type u_4)} {inst : RealScalar R}
  {_ : Scalar R K} {_ : VectorType.Base X n K} [self : VectorType.Dense X] [InjectiveGetElem X n]

@[fun_prop]
theorem ofFn.arg_f.IsLineaMap_rule : IsLinearMap K (fun f : n → K => ofFn (coll:=X) f) := by
  constructor <;> (intros; ext i; simp[vector_to_spec])

@[fun_prop]
theorem ofFn.arg_f.Continuous_rule : Continuous (fun f : n → K => ofFn (coll:=X) f) := by
  have h : (fun (x : n → K) => ofFn (coll:=X) x) = fun (f : n → K) =>ₗ[K] ofFn (coll:=X) f := rfl
  rw[h];
  apply LinearMap.continuous_of_finiteDimensional

@[fun_prop]
theorem ofFn.arg_f.IsContinuousLineaMap_rule : IsContinuousLinearMap K (fun f : n → K => ofFn (coll:=X) f) := by
  constructor
  · fun_prop
  · dsimp only [autoParam]; fun_prop

#generate_linear_map_simps ofFn.arg_f.IsLineaMap_rule

-- fderiv
@[fun_trans]
theorem ofFn.arg_f.fderiv_rule :
    fderiv K (fun f : n → K => ofFn (coll:=X) f) = fun _ => fun df =>L[K] ofFn (coll:=X) df := by
  fun_trans

@[data_synth]
theorem ofFn.arg_f.HasFDerivAt_rule (f₀ : n → K) :
    HasFDerivAt (𝕜:=K) (fun f : n → K => ofFn (coll:=X) f) (fun df =>L[K] ofFn df) f₀ := by
  apply hasFDerivAt_from_isContinuousLinearMap

-- forward AD
@[fun_trans]
theorem ofFn.arg_f.fwdFDeriv_rule :
    fwdFDeriv K (fun f : n → K => ofFn (coll:=X) f) = fun f df => (ofFn f, ofFn df) := by
  fun_trans


-- adjoint
@[fun_trans]
theorem ofFn.arg_f.adjoint_rule :
    adjoint K (fun f : n → K => ofFn (coll:=X) f)
    =
    fun x (i : n) => x[i] := by
  funext f
  apply AdjointSpace.ext_inner_left K
  intro z
  rw[← adjoint_ex _ (by fun_prop)]
  simp[vector_to_spec, Finset.sum_ite, Finset.filter_eq,Inner.inner,sum_to_finset_sum]


@[data_synth]
theorem ofFn.arg_f.HasAdjoint_rule :
    HasAdjoint K (fun f : n → K => ofFn (coll:=X) f) (fun x i => x[i]) := by
  constructor
  case adjoint => intros; simp[vector_to_spec, Inner.inner,sum_to_finset_sum]
  case is_linear => fun_prop

@[data_synth]
theorem ofFn.arg_f.HasAdjointUpdate_rule :
    HasAdjointUpdate K (fun f : n → K => ofFn (coll:=X) f) (fun x f i => f i + x[i]) := by
  apply hasAdjointUpdate_from_hasAdjoint
  case adjoint => data_synth
  case simp => intros; funext i; simp

-- reverse AD
@[fun_trans]
theorem ofFn.arg_f.revFDeriv_rule :
    revFDeriv K (fun f : n → K => ofFn (coll:=X) f)
    =
    fun f =>
      (ofFn f, fun dx i => dx[i]) := by
  unfold revFDeriv
  autodiff
  simp

@[data_synth]
theorem ofFn.arg_f.HasRevFDeriv_rule :
    HasRevFDeriv K (fun f : n → K => ofFn (coll:=X) f) (fun f => (ofFn f, fun dx i => dx[i])) := by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl

@[data_synth]
theorem ofFn.arg_f.HasRevFDerivUpdate_rule :
    HasRevFDerivUpdate K (fun f : n → K => ofFn (coll:=X) f) (fun f => (ofFn f, fun dx f' i => f' i + dx[i])) := by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl
