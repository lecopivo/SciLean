module

public import SciLean.Analysis.Calculus.HasRevFDeriv
public import SciLean.Analysis.Calculus.HasFwdFDeriv
public import SciLean.Analysis.Calculus.ContDiff

public import SciLean.Tactic.DataSynth.DefDataSynth
public import SciLean.Meta.GenerateFunTrans
public import SciLean.Tactic.ConvAssign
public import SciLean.Lean.ToSSA
public import SciLean.Meta.GenerateFunProp

@[expose] public section



open SciLean

macro "hasFDerivAt_from_linear" : tactic =>
  `(tactic| (apply hasFDerivAt_from_isContinuousLinearMap; fun_prop))

open Lean Parser Tactic Conv

macro "hasFwdFDeriv_from_def" "=>" cleanUp:convSeq : tactic =>
  `(tactic|
    (apply hasFwdFDeriv_from_hasFDerivAt
     case deriv => intros; data_synth
     case simp => intros; (conv => rhs; ($cleanUp))))


macro "hasAdjointUpdate_from_adjoint" "=>" cleanUp:convSeq : tactic =>
  `(tactic|
    (apply hasAdjointUpdate_from_hasAdjoint
     case adjoint => data_synth
     case simp => intros; (conv => rhs; ($cleanUp))))

macro "hasRevFDeriv_from_def" "=>" cleanUp:convSeq : tactic =>
  `(tactic|
    (apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
     case deriv => intros; data_synth
     case adjoint => intros; (try simp); data_synth
     case simp => intros; (conv => rhs; ($cleanUp))))

macro "hasRevFDerivUpdate_from_def" "=>" cleanUp:convSeq : tactic =>
  `(tactic|
    (apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
     case deriv => intros; data_synth
     case adjoint => intros; (try simp); data_synth
     case simp => intros; (conv => rhs; ($cleanUp))))
