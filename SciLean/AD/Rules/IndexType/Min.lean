
module

public import SciLean.Analysis.Calculus.HasRevFDeriv
public import SciLean.Analysis.Calculus.HasFwdFDeriv

@[expose] public section



namespace SciLean.IndexType

set_option linter.unusedVariables false

variable
  {𝕜 : Type u} [RealScalar 𝕜] [Top 𝕜]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {U : Type*} [NormedAddCommGroup U] [AdjointSpace 𝕜 U]
  -- {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {I : Type v} {nI : ℕ} [IndexType I nI] [Fold.{v,u} I] [Fold.{v,max u v} I] [Inhabited I]


@[fun_prop]
theorem min.arg_f.Differentiable_rule
    (f : W → I → 𝕜) (hf : (fun w => argMin (f w)).IsConstant) :
    Differentiable 𝕜 (fun w => min (f w)) := sorry_proof

-- @[data_synth]
-- theorem min.arg_f.HasFDerivAt_comp_rule (w₀ : W)
--     (f : W → I → 𝕜) (f' : I → _) (hf : ∀ i, HasFDerivAt (𝕜:=𝕜) (f · i) (f' i) w₀):
--     HasFDerivAt
--       (fun w  => min (f w))
--       (fun dw =>L[𝕜] ∑ᴵ i, f' i dw) w₀ := by
--   sorry_proof


@[data_synth]
theorem min.arg_f.HasFwdDeriv_rule
    (f : W → I → 𝕜) (f' : I → W → W → 𝕜×𝕜)
    (hf : ∀ i, HasFwdFDeriv 𝕜 (f · i) (f' i)) (hf' : (fun w => argMin (f w)).IsConstant) :
    HasFwdFDeriv 𝕜
      (fun w => min (f w))
      (fun w dw =>
        let i := argMin (f w)
        let' (xi,dxi) := f' i w dw
        (xi,dxi)) := by
  sorry_proof



variable
  {W : Type*} [NormedAddCommGroup W] [AdjointSpace 𝕜 W]


@[data_synth]
theorem min.arg_f.HasRevDeriv_rule
    (f : W → I → 𝕜) (f' : I → _)
    (hf : ∀ i, HasRevFDeriv 𝕜 (f · i) (f' i)) (hf' : (fun w => argMin (f w)).IsConstant) :
    HasRevFDeriv 𝕜
      (fun w => min (f w))
      (fun w =>
        let i := argMin (f w)
        let' (xi,dfi) := f' i w
        (xi, fun dy =>
          let dw := dfi dy
          dw)) := by
  sorry_proof


@[data_synth]
theorem min.arg_f.HasRevDerivUpdate_rule
    (f : W → I → 𝕜) (f' : I → _)
    (hf : ∀ i, HasRevFDerivUpdate 𝕜 (f · i) (f' i)) (hf' : (fun w => argMin (f w)).IsConstant) :
    HasRevFDerivUpdate 𝕜
      (fun w => min (f w))
      (fun w =>
        let i := argMin (f w)
        let' (xi,dfi) := f' i w
        (xi, fun dy dw =>
          let dw := dfi dy dw
          dw)) := by
  obtain ⟨hval, df, hd, ha⟩ :=
    min.arg_f.HasRevDeriv_rule (𝕜:=𝕜) f
      (f' := fun i w => ((f' i w).1, fun dy => (f' i w).2 dy 0))
      (fun i => (hf i).toHasRevFDeriv) hf'
  refine hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate hd
    (df' := fun w dy dw => (f' (argMin (f w)) w).2 dy dw)
    (fun w => hasAdjointUpdate_from_hasAdjoint (ha w)
      (fun dy dw => (hf (argMin (f w))).apply_eq_zero_add w dy dw)) ?_
  funext w
  exact Prod.ext (hval w) rfl
