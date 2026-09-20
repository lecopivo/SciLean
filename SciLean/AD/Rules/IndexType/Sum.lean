module

public import SciLean.Analysis.Calculus.HasRevFDeriv
public import SciLean.Analysis.Calculus.HasFwdFDeriv

@[expose] public section



namespace SciLean.IndexType

set_option linter.unusedVariables false

variable
  {𝕜 : Type*} [RCLike 𝕜]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {I : Type*} {nI : ℕ} [IndexType I nI] [Fold I]


-- @[fun_prop] -- already exists
theorem sum.arg_f.IsContinuousLinearMap_rule' :
    IsContinuousLinearMap 𝕜 (fun f : I → X => sum f) := by fun_prop


@[fun_prop]
theorem sum.arg_f.Differentiable_rule :
    Differentiable 𝕜 (fun f : I → X => sum f) := by fun_prop


@[data_synth]
theorem sum.arg_f.HasFDerivAt_comp_rule (w₀ : W)
    (f : W → I → X) (f' : I → _) (hf : ∀ i, HasFDerivAt (𝕜:=𝕜) (f · i) (f' i) w₀):
    HasFDerivAt
      (fun w  => sum (f w))
      (fun dw =>L[𝕜] ∑ᴵ i, f' i dw) w₀ := by
  sorry_proof


-- @[data_synth] -- already exists
theorem sum.arg_f.HasFDerivAt_simp_rule' (f₀ : I → X) :
    HasFDerivAt (fun f : I → X => sum (fun i => f i)) (fun df : I → X =>L[𝕜] sum df) f₀ := by
  apply hasFDerivAt_from_isContinuousLinearMap


@[data_synth]
theorem sum.arg_f.HasFwdDeriv_rule
    (f : W → I → X) (f' : I → W → W → X×X) (hf : ∀ i, HasFwdFDeriv 𝕜 (f · i) (f' i)) :
    HasFwdFDeriv 𝕜
      (fun w => sum (f w))
      (fun w dw =>
        let' (x,dx) := ∑ᴵ i, f' i w dw
        (x,dx)) := by
  sorry_proof


@[data_synth]
theorem sum.arg_f.HasRevFDeriv_rule
    {W} [NormedAddCommGroup W] [AdjointSpace 𝕜 W]
    {X : Type*} [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
    {I : Type*} {nI} [IndexType I nI] [Fold I]
    (f : W → I → X) {f' : I → _} (hf : ∀ i, HasRevFDerivUpdate 𝕜 (f · i) (f' i))  :
    HasRevFDeriv 𝕜
      (fun w => sum (f w))
      (fun w =>
        let s := ∑ᴵ i, (f w i)
        (s, fun dx =>
          let dw := IndexType.fold .full (init := (0:W)) (fun i dw =>
            let dw := (f' i w).2 dx dw
            dw)
          dw)) := sorry_proof


@[data_synth]
theorem sum.arg_f.HasRevFDerivUpdate_rule
    {W} [NormedAddCommGroup W] [AdjointSpace 𝕜 W]
    {X : Type*} [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
    {I : Type*} {nI} [IndexType I nI] [Fold I]
    (f : W → I → X) {f' : I → _} (hf : ∀ i, HasRevFDerivUpdate 𝕜 (f · i) (f' i))  :
    HasRevFDerivUpdate 𝕜
      (fun w => sum (f w))
      (fun w =>
        let s := ∑ᴵ i, (f w i)
        (s, fun dx dw =>
          let dw := IndexType.fold .full (init := dw) (fun i dw =>
            let dw := (f' i w).2 dx dw
            dw)
          dw)) := sorry_proof


theorem sum.arg_f.HasRevFDeriv_rule_scalar
    {K} [RCLike K]
    {W} [NormedAddCommGroup W] [AdjointSpace K W]
    {I : Type*} {nI} [IndexType I nI] [Fold I]
    (f : W → I → K) {f' : I → _} (hf : ∀ i, HasRevFDerivUpdate K (f · i) (f' i))  :
    HasRevFDeriv K
      (fun w => sum (f w))
      (fun w =>
        let' (s,dw) := IndexType.fold .full (init := ((0 : K), (0:W)))
          (fun (i : I) sdw =>
            let' (s,dw) := sdw
            let' (x,df) := f' i w
            let s := s + x
            (s, df 1 dw))
        (s, fun dx => dx•dw)) := sorry_proof


theorem sum.arg_f.HasRevFDerivUpdate_rule_scalar
    {K} [RCLike K]
    {W} [NormedAddCommGroup W] [AdjointSpace K W]
    {I : Type*} {nI} [IndexType I nI] [Fold I]
    (f : W → I → K) {f' : I → _} (hf : ∀ i, HasRevFDerivUpdate K (f · i) (f' i))  :
    HasRevFDerivUpdate K
      (fun w => sum (f w))
      (fun w =>
        let' (s,dw) := IndexType.fold .full (init := ((0 : K), (0:W)))
          (fun (i : I) sdw =>
            let' (s,dw) := sdw
            let' (x,df) := f' i w
            let s := s + x
            (s, df 1 dw))
        (s, fun dx dw' => dw' + dx•dw)) := sorry_proof
