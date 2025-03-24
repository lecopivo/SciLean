import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.Analysis.Calculus.ContDiff

import SciLean.Meta.GenerateFunProp
import SciLean.Meta.GenerateFunTrans
import SciLean.Lean.ToSSA

open ComplexConjugate

namespace SciLean.Scalar

set_option deprecated.oldSectionVars true

variable
  {R C} [Scalar R C] [RealScalar R]


--------------------------------------------------------------------------------
-- Identities ------------------------------------------------------------------
--------------------------------------------------------------------------------

open Scalar in
@[simp, simp_core]
theorem add_sin2_cos2_eq_one (x : C) : sin x * sin x + cos x * cos x = 1 :=
 sorry_proof

open Scalar in
@[simp, simp_core]
theorem add_cos2_sin2_eq_one (x : C) : cos x * cos x + sin x * sin x = 1 :=
 sorry_proof


--------------------------------------------------------------------------------
-- Sin -------------------------------------------------------------------------
--------------------------------------------------------------------------------

def_fun_prop sin in x with_transitive : Differentiable K by sorry_proof
def_fun_prop sin in x with_transitive : ContDiff K ⊤ by sorry_proof

abbrev_fun_trans sin in x : fderiv K by equals (fun x => fun dx =>L[K] dx • cos x) => sorry_proof
abbrev_fun_trans sin in x : fwdFDeriv K by unfold fwdFDeriv; fun_trans; to_ssa
abbrev_fun_trans sin in x : revFDeriv K by unfold revFDeriv; fun_trans; to_ssa



--------------------------------------------------------------------------------
-- Cos -------------------------------------------------------------------------
--------------------------------------------------------------------------------

def_fun_prop cos in x with_transitive : Differentiable K by sorry_proof
def_fun_prop cos in x with_transitive : ContDiff K ⊤ by sorry_proof

abbrev_fun_trans cos in x : fderiv K by equals (fun x => fun dx =>L[K] (-dx) • sin x) => sorry_proof
abbrev_fun_trans cos in x : fwdFDeriv K by unfold fwdFDeriv; fun_trans; to_ssa
abbrev_fun_trans cos in x : revFDeriv K by unfold revFDeriv; fun_trans; to_ssa


--------------------------------------------------------------------------------
-- Tanh -------------------------------------------------------------------------
--------------------------------------------------------------------------------

def_fun_prop tanh in x with_transitive : Differentiable K by sorry_proof
def_fun_prop tanh in x with_transitive : ContDiff K ⊤ by sorry_proof

abbrev_fun_trans tanh in x : fderiv K by equals (fun x => fun dx =>L[K] let t := tanh x; dx * (1 - t^2)) => sorry_proof
abbrev_fun_trans tanh in x : fwdFDeriv K by unfold fwdFDeriv; fun_trans; to_ssa; lsimp
abbrev_fun_trans tanh in x : revFDeriv K by unfold revFDeriv; fun_trans; to_ssa; lsimp
