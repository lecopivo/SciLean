import SciLean.Analysis.SpecialFunctions.Inner
import SciLean.Data.DataArray.TensorOperations

import SciLean.AD.Rules.Common

import SciLean.AD.Rules.Log
import SciLean.AD.Rules.Exp

import SciLean.Tactic.UnsafeAD

namespace SciLean

set_option linter.unusedTactic false

open DataArrayN


def_fun_prop logsumexp in x
    with_transitive
    [BLAS (DataArray R) R R] [NormedAddCommGroup X] [AdjointSpace R X]
    /- todo: add compatibility condition between `X` and `R^[ι]` -/ :
    ContDiff R ⊤ by
  unfold logsumexp
  sorry_proof

-- todo: add compatibility condition between `X` and `R^[ι
data_synth_variable
  [BLAS (DataArray R) R R] [NormedAddCommGroup X] [AdjointSpace R X]
  [Fold ι] [Fold ι] [Fold I]


abbrev_data_synth logsumexp in x (x₀ : X^[I]) :
  (HasFDerivAt (𝕜:=R) · · x₀) by
  conv => enter [2]; assign (fun (dx : X^[I]) =>L[R] let x' := x₀.softmax; ⟪dx, x'⟫[R])
  sorry_proof

abbrev_data_synth logsumexp in x :
    (HasFwdFDeriv R ·
      (fun x dx =>
        let' (w,x') := x.logsumexpSoftmax
        let dx' := ⟪dx,x'⟫[R]
        (w,dx'))) by
  sorry_proof

abbrev_data_synth logsumexp in x :
  (HasRevFDeriv R ·
    (fun x =>
      let' (w,x') := x.logsumexpSoftmax
      (w, fun dk =>
        let dx := (starRingEnd R) dk • x'
        dx))) by
  sorry_proof

abbrev_data_synth logsumexp in x :
  (HasRevFDerivUpdate R ·
   (fun x =>
      let' (w,x') := x.logsumexpSoftmax
      (w, fun dk dx' =>
        let dx := dx' + ((starRingEnd R) dk) • x'
        dx))) by
  sorry_proof
