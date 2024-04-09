import SciLean.Core.Distribution.ParametricDistribDeriv
import SciLean.Core.Distribution.SurfaceDirac
import SciLean.Core.Distribution.Eval
import SciLean.Core.Integral.Substitution
import SciLean.Core.Integral.ParametricInverse
import SciLean.Core.Integral.Frontier
import SciLean.Core

import SciLean.Util.RewriteBy

open MeasureTheory Set BigOperators

namespace SciLean

variable
  {R} [RealScalar R]
  {W} [SemiHilbert R W]
  {X} [SemiHilbert R X]
  {Y} [SemiHilbert R Y] -- [Module ℝ Y]
  {Z} [SemiHilbert R Z] -- [Module ℝ Z]

set_default_scalar R


attribute [ftrans_simp]
  FiniteDimensional.finrank_self FiniteDimensional.finrank_prod
  mem_setOf_eq not_le ite_mul mul_ite mul_neg mul_one setOf_eq_eq_singleton mem_Ioo
  Finset.card_singleton PUnit.default_eq_unit Finset.univ_unique Finset.sum_const
  preimage_id'

open FiniteDimensional in
@[simp, ftrans_simp]
theorem _root_.FiniteDimensional.finrank_unit : finrank R Unit = 0 := by sorry_proof

variable [MeasureSpace R] -- [Module ℝ R]

def foo1 (t' : R) := (∂ (t:=t'), ∫' (x:R) in Ioo 0 1, if x ≤ t then (1:R) else 0)
  rewrite_by
    fun_trans only [scalarGradient, scalarCDeriv]
    simp only [ftrans_simp]
    simp only [action_push, ftrans_simp]

theorem foo1_spec (t : R) :
    foo1 t = if 0 < t ∧ t < 1 then 1 else 0 := by rfl

#eval foo1 0.5    -- 1.0
#eval foo1 (-1.0) -- 0.0
#eval foo1 2.0    -- 0.0

open Classical in

set_option pp.funBinderTypes true in

def foo2 (t' : R) := (∂ (t:=t'), ∫' (x:R) in Ioo 0 1, if x - t ≤ 0 then (1:R) else 0)
  rewrite_by
    fun_trans only [scalarGradient, scalarCDeriv]
    simp only [ftrans_simp]

    rw[surfaceDirac_substitution
        (I:=Unit) (X₁:=fun _ => Unit) (X₂:= fun _ => R)
        (p:= fun _ _ x => x)
        (ζ:= fun _ _ => t')
        (dom:= fun _ => Set.univ)
        (inv:= by intro i x₁ _; dsimp; simp) (hdim := sorry)]

    simp only [ftrans_simp]
    conv in jacobian _ _ =>
      fun_trans
    simp only [action_push, ftrans_simp]

#check instTCOr_1

theorem foo2_spec (t : R) :
    foo2 t = if 0 < t ∧ t < 1 then 1 else 0 := by rfl

#eval foo2 0.5
#eval foo2 (-1.0)
#eval foo2 2.0

set_option pp.funBinderTypes true in

def foo3 (t' : R) := (∂ (t:=t'), ∫' (x:R) in Ioo (-1) 1, if x^2 - t ≤ 0 then (1:R) else 0)
  rewrite_by assuming (_ : 0 < t')
    fun_trans only [scalarGradient, scalarCDeriv]
    simp only [ftrans_simp]

    rw[surfaceDirac_substitution
        (I:= Bool)
        (X₁:=fun _ => Unit) (X₂:= fun _ => R)
        (p:= fun _ _ x => x)
        (ζ:= fun b _ => if b then Scalar.sqrt t' else - Scalar.sqrt t')
        (dom:= fun _ => Set.univ)
        (inv:= by intro i x₁ _; dsimp; simp; sorry_proof) (hdim := sorry_proof)]

    simp only [ftrans_simp]
    conv =>
      enter [1,1,2,b,2,1,p]
      autodiff
    simp only [ftrans_simp, action_push,restrict_push]

def foo3' (t : R) := if |t| < 1 then 1/Scalar.sqrt |t| else 0

#eval foo3 0.3
#eval foo3' 0.3

#eval foo3 0.999
#eval foo3' 0.999
