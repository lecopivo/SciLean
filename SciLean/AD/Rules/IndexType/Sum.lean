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
  simp only [IndexType.sum_eq_finset_sum]
  refine hasFDerivAt_from_hasFDerivAt (HasFDerivAt.fun_sum (fun i _ => hf i)) ?_
  ext dw
  simp


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
  exact _root_.SciLean.sum.arg_f.HasFwdFDeriv_rule hf


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
          dw)) := by
  choose df hdf df' hadj hupd using fun i => (hf i).deriv
  -- the accumulating pullbacks only add to the accumulator, so the fold is just the sum
  have hfold : ∀ w dx,
      (IndexType.fold .full (init := (0:W)) (fun (i : I) (dw : W) => (f' i w).2 dx dw))
      =
      ∑ i : I, df' i w dx := by
    intro w dx
    rw [show (fun (i : I) (dw : W) => (f' i w).2 dx dw)
           = (fun (i : I) (dw : W) => dw + df' i w dx) from
          by funext i dw; rw [hupd i w dx dw]]
    show IndexType.sum (fun i => df' i w dx) = _
    rw [IndexType.sum_eq_finset_sum]
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
    (df := fun w => ∑ i : I, df i w)
    (df' := fun w dx => IndexType.fold .full (init := (0:W)) (fun i dw => (f' i w).2 dx dw))
  case deriv =>
    intro w
    simp only [IndexType.sum_eq_finset_sum]
    exact HasFDerivAt.fun_sum (fun i _ => hdf i w)
  case adjoint =>
    intro w
    constructor
    case adjoint =>
      intro dw dx
      rw [hfold w dx, sum_apply, AdjointSpace.sum_inner,
        AdjointSpace.inner_sum]
      exact Finset.sum_congr rfl fun i _ => (hadj i w).adjoint dw dx
    case is_linear => fun_prop
  case simp => rfl


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
          dw)) := by
  choose df hdf df' hadj hupd using fun i => (hf i).deriv
  refine ⟨fun w => rfl, fun w => ∑ i : I, df i w, ?_, fun w => ∑ i : I, df' i w, ?_, ?_⟩
  · intro w
    simp only [IndexType.sum_eq_finset_sum]
    exact HasFDerivAt.fun_sum (fun i _ => hdf i w)
  · intro w
    constructor
    case adjoint =>
      intro dw dx
      rw [sum_apply, sum_apply, AdjointSpace.sum_inner,
        AdjointSpace.inner_sum]
      exact Finset.sum_congr rfl fun i _ => (hadj i w).adjoint dw dx
    case is_linear => fun_prop
  · intro w dx dw
    show IndexType.fold .full (init := dw) (fun i dw => (f' i w).2 dx dw) = _
    rw [show (fun (i : I) (dw : W) => (f' i w).2 dx dw)
           = (fun (i : I) (dw : W) => dw + df' i w dx) from
          by funext i dw; rw [hupd i w dx dw]]
    rw [IndexType.fold_add_eq_add_sum, sum_apply]


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
        (s, fun dx => dx•dw)) := by
  choose df hdf df' hadj hupd using fun i => (hf i).deriv
  -- the fold just sums the pairs `(f w i, df' i w 1)`
  have hfold : ∀ w, IndexType.fold .full (init := ((0 : K), (0:W)))
      (fun (i : I) (sdw : K × W) => (sdw.1 + (f' i w).1, (f' i w).2 1 sdw.2))
      = (∑ i, f w i, ∑ i, df' i w 1) := by
    intro w
    rw [show (fun (i : I) (sdw : K × W) => (sdw.1 + (f' i w).1, (f' i w).2 1 sdw.2))
           = (fun (i : I) (sdw : K × W) => sdw + (f w i, df' i w 1)) from
          by funext i sdw; rw [hupd i w 1 sdw.2, (hf i).val w]; rfl]
    rw [IndexType.fold_add_eq_add_sum]
    ext <;> simp [Prod.fst_sum, Prod.snd_sum]
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
    (df := fun w => ∑ i : I, df i w)
    (df' := fun w dx => dx • ∑ i, df' i w 1)
  case deriv =>
    intro w
    simp only [IndexType.sum_eq_finset_sum]
    exact HasFDerivAt.fun_sum (fun i _ => hdf i w)
  case adjoint =>
    intro w
    constructor
    case adjoint =>
      intro v dx
      have e : ∀ a : K, ⟪a, dx⟫[K] = dx * ⟪a, (1:K)⟫[K] := fun a => by
        rw [← AdjointSpace.inner_smul_right, smul_eq_mul, mul_one]
      rw [sum_apply, AdjointSpace.sum_inner, AdjointSpace.inner_smul_right,
        AdjointSpace.inner_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [e, (hadj i w).adjoint v 1]
    case is_linear => fun_prop
  case simp =>
    funext w
    show _ = (sum (f w), _)
    rw [IndexType.sum_eq_finset_sum]
    exact congrArg (fun p : K × W => (p.1, fun dx : K => dx • p.2)) (hfold w)


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
        (s, fun dx dw' => dw' + dx•dw)) :=
  (sum.arg_f.HasRevFDeriv_rule_scalar f hf).toHasRevFDerivUpdate
