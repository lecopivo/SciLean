import SciLean.Core.FunctionTransformations
import SciLean.Tactic.LetNormalize2

namespace SciLean.Tactic

open Lean Meta
simproc_decl lift_lets_simproc (_) := fun e => do
  let E ← inferType e
  if (← Meta.isClass? E).isSome then return .continue
  let e ← e.liftLets2 (fun xs b => do
      if xs.size ≠ 0
      then mkLetFVars xs (← Simp.dsimp b)
      else pure b) {}
  return .visit {expr:=e}

-- todo: add option, discharger, only and [...] syntax
macro "autodiff" : conv =>
  `(conv| (fun_trans (config:={zeta:=false,singlePass:=true}) (disch:=sorry_proof) only [ftrans_simp,lift_lets_simproc, scalarGradient, scalarCDeriv];
           simp (config:={zeta:=false,failIfUnchanged:=false}) only [ftrans_simp,lift_lets_simproc]))

macro "autodiff" : tactic =>
  `(tactic| (fun_trans (config:={zeta:=false,singlePass:=true}) (disch:=sorry_proof) only [ftrans_simp,lift_lets_simproc, scalarGradient, scalarCDeriv];
             try simp (config:={zeta:=false,failIfUnchanged:=false}) only [ftrans_simp,lift_lets_simproc]))
