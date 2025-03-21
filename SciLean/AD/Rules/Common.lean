import SciLean.Analysis.Calculus.HasRevFDeriv
import SciLean.Analysis.Calculus.HasFwdFDeriv
import SciLean.Analysis.Calculus.ContDiff

import SciLean.Tactic.DataSynth.DefDataSynth
import SciLean.Meta.GenerateFunTrans
import SciLean.Tactic.ConvAssign
import SciLean.Lean.ToSSA
import SciLean.Meta.GenerateFunProp


open SciLean

macro "hasFDerivAt_from_linear" : tactic =>
  `(tactic| (apply hasFDerivAt_from_isContinuousLinearMap; fun_prop))

macro "hasFwdFDeriv_from_def" "=>" cleanUp:tactic : tactic =>
  `(tactic|
    (apply hasFwdFDeriv_from_hasFDerivAt
     case deriv => intros; data_synth
     case simp => intros; $cleanUp; rfl))


macro "hasAdjointUpdate_from_adjoint" "=>" cleanUp:tactic : tactic =>
  `(tactic|
    (apply hasAdjointUpdate_from_hasAdjoint
     case adjoint => data_synth
     case simp => intros; $cleanUp; rfl))

macro "hasRevFDeriv_from_def" "=>" cleanUp:tactic : tactic =>
  `(tactic|
    (apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
     case deriv => intros; data_synth
     case adjoint => intros; (try simp); data_synth
     case simp => intros; $cleanUp; rfl))

macro "hasRevFDerivUpdate_from_def" "=>" cleanUp:tactic : tactic =>
  `(tactic|
    (apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
     case deriv => intros; data_synth
     case adjoint => intros; (try simp); data_synth
     case simp => intros; $cleanUp; rfl))
