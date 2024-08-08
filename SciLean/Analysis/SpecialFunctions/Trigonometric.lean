import SciLean.Analysis.Calculus.FwdCDeriv
import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Analysis.Calculus.RevCDeriv
import SciLean.Analysis.Calculus.RevFDeriv

import SciLean.Core.Meta.GenerateFunProp
import SciLean.Core.Meta.GenerateFunTrans

open ComplexConjugate

namespace SciLean.Scalar

variable
  {R C} [Scalar R C] [RealScalar R]
  {W} [Vec C W]
  {U} [SemiInnerProductSpace C U]


--------------------------------------------------------------------------------
-- Identities ------------------------------------------------------------------
--------------------------------------------------------------------------------

open Scalar in
@[simp, ftrans_simp]
theorem add_sin2_cos2_eq_one (x : C) : sin x * sin x + cos x * cos x = 1 :=
 sorry_proof

open Scalar in
@[simp, ftrans_simp]
theorem add_cos2_sin2_eq_one (x : C) : cos x * cos x + sin x * sin x = 1 :=
 sorry_proof


--------------------------------------------------------------------------------
-- Sin -------------------------------------------------------------------------
--------------------------------------------------------------------------------


def_fun_prop with_transitive :
    Differentiable C (fun x : C => sin x) by sorry_proof

-- abbrev_fun_trans : fderiv C (fun x : C => sin x) by
--   equals (fun x => fun dx =>L[C] dx • cos x) => sorry_proof


@[fun_trans]
theorem sin.arg_x.fderiv_rule :
    fderiv C (fun x : C => sin x)
    =
    fun x => fun dx =>L[C] dx * cos x := sorry_proof

-- abbrev_fun_trans : fwdFDeriv C (fun x : C => sin x) by
--   unfold fwdFDeriv; fun_trans

@[fun_trans]
theorem sin.arg_x.fwdFDeriv_rule :
    fwdFDeriv C (fun x : C => sin x)
    =
    fun x dx => (sin x, dx * cos x) := by unfold fwdFDeriv; fun_trans

-- abbrev_fun_trans : revFDeriv C (fun x : C => sin x) by
--   unfold revFDeriv; fun_trans

@[fun_trans]
theorem sin.arg_x.revFDeriv_rule :
    revFDeriv C (fun x : C => sin x)
    =
    fun x =>
      (sin x,
       fun dy =>
         let s := conj cos x
         s * dy) := by
  unfold revFDeriv
  fun_trans


def_fun_prop with_transitive :
    HasAdjDiff C (fun x : C => sin x) by sorry_proof

-- abbrev_fun_trans : cderiv C (fun x : C => sin x) by
--   equals (fun x dx => dx • cos x) => sorry_proof

@[fun_trans]
theorem sin.arg_x.cderiv_rule :
    cderiv C (fun x : C => sin x)
    =
    fun x dx => dx * cos x := sorry_proof

-- abbrev_fun_trans : fwdCDeriv C (fun x : C => sin x) by
--   unfold fwdCDeriv; fun_trans

@[fun_trans]
theorem sin.arg_x.fwdCDeriv_rule :
    fwdCDeriv C (fun x : C => sin x)
    =
    fun x dx => (sin x, dx * cos x) := by unfold fwdCDeriv; fun_trans

-- abbrev_fun_trans : revCDeriv C (fun x : C => sin x) by
--   unfold revCDeriv; fun_trans

@[fun_trans]
theorem sin.arg_x.revCDeriv_rule :
    revCDeriv C (fun x : C => sin x)
    =
    fun x =>
      (sin x,
       fun dy =>
         let s := conj cos x
         s * dy) := by
  unfold revCDeriv
  fun_trans


--------------------------------------------------------------------------------
-- Cos -------------------------------------------------------------------------
--------------------------------------------------------------------------------

def_fun_prop with_transitive :
    Differentiable C (fun x : C => cos x) by sorry_proof

-- abbrev_fun_trans : fderiv C (fun x : C => cos x) by
--   equals (fun x => fun dx =>L[C] dx • cos x) => sorry_proof

@[fun_trans]
theorem cos.arg_x.fderiv_rule :
    fderiv C (fun x : C => cos x)
    =
    fun x => fun dx =>L[C] - dx * cos x := sorry_proof

@[fun_trans]
theorem cos.arg_x.fwdFDeriv_rule :
    fwdFDeriv C (fun x : C => cos x)
    =
    fun x dx => (cos x, - dx * cos x) := by unfold fwdFDeriv; fun_trans

@[fun_trans]
theorem cos.arg_x.revFDeriv_rule :
    revFDeriv C (fun x : C => cos x)
    =
    fun x =>
      (cos x,
       fun dy =>
         let s := conj cos x
         (- s * dy)) := by
  unfold revFDeriv
  fun_trans


def_fun_prop with_transitive :
    HasAdjDiff C (fun x : C => cos x) by sorry_proof

@[fun_trans]
theorem cos.arg_x.cderiv_rule :
    cderiv C (fun x : C => cos x)
    =
    fun x dx => - dx * cos x := sorry_proof

@[fun_trans]
theorem cos.arg_x.fwdCDeriv_rule :
    fwdCDeriv C (fun x : C => cos x)
    =
    fun x dx => (cos x, - dx * cos x) := by unfold fwdCDeriv; fun_trans

@[fun_trans]
theorem cos.arg_x.revCDeriv_rule :
    revCDeriv C (fun x : C => cos x)
    =
    fun x =>
      (cos x,
       fun dy =>
         let s := conj cos x
         (- s * dy)) := by
  unfold revCDeriv
  fun_trans


--------------------------------------------------------------------------------
-- Tanh -------------------------------------------------------------------------
--------------------------------------------------------------------------------

def_fun_prop with_transitive :
    Differentiable C (fun x : C => tanh x) by sorry_proof

-- abbrev_fun_trans : fderiv C (fun x : C => tanh x) by
--   equals (fun x => fun dx =>L[C] dx • tanh x) => sorry_proof

@[fun_trans]
theorem tanh.arg_x.fderiv_rule :
    fderiv C (fun x : C => tanh x)
    =
    fun x => fun dx =>L[C]
      let t := tanh x
      dx * (1 - t^2) := sorry_proof

@[fun_trans]
theorem tanh.arg_x.fwdFDeriv_rule :
    fwdFDeriv C (fun x : C => tanh x)
    =
    fun x dx =>
      let t := tanh x
      (t, dx * (1 - t^2)) := by unfold fwdFDeriv; fun_trans

@[fun_trans]
theorem tanh.arg_x.revFDeriv_rule :
    revFDeriv C (fun x : C => tanh x)
    =
    fun x =>
      let t := tanh x
      (t,
       fun dy =>
         let s := conj t
         ((1 - s^2) * dy)) := by
  unfold revFDeriv
  fun_trans


def_fun_prop with_transitive :
    HasAdjDiff C (fun x : C => tanh x) by sorry_proof

@[fun_trans]
theorem tanh.arg_x.cderiv_rule :
    cderiv C (fun x : C => tanh x)
    =
    fun x dx =>
      let t := tanh x
      dx * (1 - t^2) := sorry_proof

@[fun_trans]
theorem tanh.arg_x.fwdCDeriv_rule :
    fwdCDeriv C (fun x : C => tanh x)
    =
    fun x dx =>
      let t := tanh x
      (t, dx * (1 - t^2)) := by unfold fwdCDeriv; fun_trans

@[fun_trans]
theorem tanh.arg_x.revCDeriv_rule :
    revCDeriv C (fun x : C => tanh x)
    =
    fun x =>
      let t := tanh x
      (t,
       fun dy =>
         let s := conj t
         ((1 - s^2) * dy)) := by
  unfold revCDeriv
  fun_trans
