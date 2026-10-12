module

public import SciLean.Analysis.Calculus.HasRevFDeriv
public import SciLean.Analysis.Calculus.HasFwdFDeriv

@[expose] public section



namespace SciLean.IndexType

set_option linter.unusedVariables false

variable
  {𝕜 : Type u} [RealScalar 𝕜] [Bot 𝕜]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {U : Type*} [NormedAddCommGroup U] [AdjointSpace 𝕜 U]
  -- {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {I : Type v} {nI : ℕ} [IndexType I nI] [Fold.{v,u} I] [Fold.{v,max u v} I] [Inhabited I]


@[fun_prop]
theorem max.arg_f.Differentiable_rule
    (f : W → I → 𝕜) (hf : Function.IsConstant (fun w => argMax (f w))) :
    Differentiable 𝕜 (fun w => max (f w)) := sorry_proof

-- @[data_synth]
-- theorem max.arg_f.HasFDerivAt_comp_rule (w₀ : W)
--     (f : W → I → X) (f' : I → _) (hf : ∀ i, HasFDerivAt (𝕜:=𝕜) (f · i) (f' i) w₀):
--     HasFDerivAt
--       (fun w  => max (f w))
--       (fun dw =>L[𝕜] ∑ᴵ i, f' i dw) w₀ := by
--   sorry_proof


@[data_synth]
theorem max.arg_f.HasFwdDeriv_rule
    (f : W → I → 𝕜) (f' : I → W → W → 𝕜×𝕜)
    (hf : ∀ i, HasFwdFDeriv 𝕜 (f · i) (f' i)) (hf' : (fun w => argMax (f w)).IsConstant) :
    HasFwdFDeriv 𝕜
      (fun w => max (f w))
      (fun w dw =>
        let i := argMax (f w)
        let' (xi,dxi) := f' i w dw
        (xi,dxi)) := by
  sorry_proof


variable
  {W : Type*} [NormedAddCommGroup W] [AdjointSpace 𝕜 W]


@[data_synth]
theorem max.arg_f.HasRevDeriv_rule
    (f : W → I → 𝕜) (f' : I → _)
    (hf : ∀ i, HasRevFDeriv 𝕜 (f · i) (f' i)) (hf' : (fun w => argMax (f w)).IsConstant) :
    HasRevFDeriv 𝕜
      (fun w => max (f w))
      (fun w =>
        let i := argMax (f w)
        let' (xi,dfi) := f' i w
        (xi, fun dy =>
          let dw := dfi dy
          dw)) := by
  sorry_proof


@[data_synth]
theorem max.arg_f.HasRevDerivUpdate_rule
    (f : W → I → 𝕜) (f' : I → _)
    (hf : ∀ i, HasRevFDerivUpdate 𝕜 (f · i) (f' i)) (hf' : (fun w => argMax (f w)).IsConstant) :
    HasRevFDerivUpdate 𝕜
      (fun w => max (f w))
      (fun w =>
        let i := argMax (f w)
        let' (xi,dfi) := f' i w
        (xi, fun dy dw =>
          let dw := dfi dy dw
          dw)) := by
  sorry_proof
