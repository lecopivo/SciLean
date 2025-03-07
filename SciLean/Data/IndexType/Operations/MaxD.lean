import SciLean.Data.IndexType.Operations
import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Analysis.AdjointSpace.HasAdjoint
import SciLean.Analysis.Calculus.HasRevFDeriv
-- import SciLean.Tactic.DataSynth.HasRevFDerivUpdate
import SciLean.Tactic.DFunLikeCoeZetaDelta
import SciLean.Meta.GenerateFunTrans
import SciLean.Tactic.ConvAssign
import SciLean.Lean.ToSSA

namespace SciLean

set_option linter.unusedVariables false

-- TODO: This is not completely true!!! We should have only `DifferentiableAt
@[fun_prop]
theorem IndexType.maxD.arg_f.Differentiable_rule
    {R} [RealScalar R] {I} [IndexType I] (x₀ : R) :
    Differentiable R (fun f : I → R => IndexType.maxD f x₀) := sorry_proof


@[data_synth]
theorem IndexType.maxD.arg_f.HasRevFDeriv_rule
    {R} [RealScalar R] {I} [IndexType I] [Inhabited I] [DecidableEq I]
    {W} [NormedAddCommGroup W] [AdjointSpace R W]
    (f : W → (I → R)) (f' : I → _) (hf' : ∀ i, HasRevFDeriv R (f · i) (f' i))
    (x₀ : R) :
    HasRevFDeriv R (fun w : W => IndexType.maxD (f w) x₀)
      (fun w =>
        let i := IndexType.argMax (f w)
        let' (x,df) := f' i w
        (x, fun dxi =>
          let dw := df dxi
          dw)) := sorry_proof

@[data_synth]
theorem IndexType.maxD.arg_f.HasRevFDerivUpdate_rule
    {R} [RealScalar R] {I} [IndexType I] [Inhabited I] [DecidableEq I]
    {W} [NormedAddCommGroup W] [AdjointSpace R W]
    (f : W → (I → R)) (f' : I → _) (hf' : ∀ i, HasRevFDerivUpdate R (f · i) (f' i))
    (x₀ : R) :
    HasRevFDerivUpdate R (fun w : W => IndexType.maxD (f w) x₀)
      (fun w =>
        let i := IndexType.argMax (f w)
        let' (x,df) := f' i w
        (x, fun dxi dw =>
          let dw := df dxi dw
          dw)) := sorry_proof
