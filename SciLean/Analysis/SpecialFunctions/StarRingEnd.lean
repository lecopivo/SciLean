import SciLean.Analysis.Normed.IsContinuousLinearMap

open SciLean ComplexConjugate

-- todo: move this
open ComplexConjugate in
@[simp, simp_core]
theorem SciLean.Scalar.starRingEnd_make {R K} [RealScalar R] [Scalar R K] (a b : R) :
  conj (Scalar.make (K:=K) a b) = Scalar.make a (-b) := by sorry_proof


@[fun_prop]
theorem Star.star.arg_a0.IsLinearMap_rule_scalar {R K} [RealScalar R] [Scalar R K] [ScalarSMul R K] :
    IsLinearMap R (fun x : K => star x) := by
  constructor
  · apply star_add
  · intro c x
    calc _ = star (c • (1:K) • x) := by simp
         _ = star ((c • (1:K)) • x) := by rw[smul_assoc]
         _ = star (c • (1:K)) • star x := by rw[star_smul]
         _ = c • star x := by simp[ScalarSMul.smul_eq_mul_make]

@[fun_prop]
theorem Star.star.arg_a0.IsContinuousLinearMap_rule_scalar {R K} [RealScalar R] [Scalar R K] [ScalarSMul R K] :
    IsContinuousLinearMap R (fun x : K => star x) := by
  constructor
  · fun_prop
  · dsimp only [autoParam]; fun_prop

example {R} [RCLike R] : ContinuousStar R := by infer_instance

@[fun_prop]
theorem starRingEnd.arg_a0.Continuous_rule_scalar {R K} [Scalar R K] :
    Continuous (fun x : K => conj x) := by
  simp only [← RCLike.star_def]
  fun_prop

@[fun_prop]
theorem starRingEnd.arg_a0.IsLinearMap_rule_scalar {R K} [RealScalar R] [Scalar R K] [ScalarSMul R K] :
    IsLinearMap R (fun x : K => conj x) := by
  simp only [← RCLike.star_def]
  fun_prop

#generate_linear_map_simps starRingEnd.arg_a0.IsLinearMap_rule_scalar

@[fun_prop]
theorem starRingEnd.arg_a0.IsContinuousLinearMap_rule_scalar {R K} [RealScalar R] [Scalar R K] [ScalarSMul R K] :
    IsContinuousLinearMap R (fun x : K => conj x) := by
  simp only [← RCLike.star_def]
  fun_prop
