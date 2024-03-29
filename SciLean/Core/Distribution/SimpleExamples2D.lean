import SciLean.Core.Distribution.ParametricDistribDeriv
import SciLean.Core.Distribution.SurfaceDirac
import SciLean.Core.Distribution.Eval
-- import SciLean.Core.Integral.Substitution
-- import SciLean.Core.Integral.ParametricInverse
-- import SciLean.Core.Integral.Frontier

import SciLean.Core.FunctionTransformations.Preimage

import SciLean.Tactic.IfPull

import SciLean.Core

import SciLean.Util.RewriteBy

open MeasureTheory Set BigOperators

namespace SciLean

variable
  {R} [RealScalar R] [MeasureSpace R]
  {W} [SemiHilbert R W]
  {X} [SemiHilbert R X]
  {Y} [SemiHilbert R Y] -- [Module ℝ Y]
  {Z} [SemiHilbert R Z] -- [Module ℝ Z]

set_default_scalar R

attribute [ftrans_simp]
  FiniteDimensional.finrank_self FiniteDimensional.finrank_prod
  not_le ite_mul mul_ite mul_neg mul_one setOf_eq_eq_singleton
  Finset.card_singleton PUnit.default_eq_unit Finset.univ_unique Finset.sum_const
  preimage_id'
  mem_setOf_eq mem_ite_empty_right mem_inter_iff mem_ite_empty_right mem_univ mem_Ioo
  and_true


def foo1 (t' : R) :=
  derive_random_approx
    (∂ (t:=t'), ∫' (xy : R×R) in (Ioo 0 1).prod (Ioo 0 1), if xy.1 ≤ t then (1:R) else 0)
  by
    fun_trans only [scalarGradient, scalarCDeriv]
    simp only [ftrans_simp]

    rw[surfaceDirac_substitution
        (I:= Unit)
        (X₁:=fun _ => R) (X₂:= fun _ => R)
        (p:= fun _ y x => (x,y))
        (ζ:= fun b y => t')
        (dom:= fun _ => Set.univ)
        (inv:= by intro i x₁ _; dsimp; simp) (hdim := sorry_proof)]

    autodiff; autodiff
    simp only [ftrans_simp,action_push]

    simp (disch:=sorry) only [ftrans_simp]
    rand_pull_E

#eval Rand.print_mean_variance (foo1 0.3) 100 " of foo1"


noncomputable
def foo := (fun x : R => (fun (z y : R) => (if x < 1 then x*y*z else x + y + z)).toDistribution (R:=R))
  rewrite_by
    simp only [Tactic.if_pull]


-- #exit

def foo1' (t' : R) :=
  derive_random_approx
    (∂ (t:=t'), ∫' (x : R) in Ioo 0 1, ∫' (y : R) in Ioo 0 1, if x ≤ t then (1:R) else 0)
  by
    fun_trans only [scalarGradient, scalarCDeriv]
    simp only [ftrans_simp]
    simp only [Tactic.if_pull]
    fun_trans only [scalarGradient, scalarCDeriv,ftrans_simp]
    simp (disch:=sorry) only [action_push, ftrans_simp]
    rand_pull_E
    simp

#eval Rand.print_mean_variance (foo1' 0.3) 100 " of foo1'"


-- open Scalar in
-- def foo1'' (t' : R) :=
--   derive_random_approx
--     (∂ (t:=t'), ∫' (x : R) in Ioo 0 1, sqrt (∫' (y : R) in Ioo 0 1, if x ≤ t then (1:R) else 0))
--   by
--     fun_trans only [scalarGradient, scalarCDeriv, if_pull, ftrans_simp]
--     simp only [action_push, ftrans_simp]


def foo2 (t' : R) :=
  derive_random_approx
    (∂ (t:=t'), ∫' (xy : R×R) in (Ioo 0 1).prod (Ioo 0 1), if xy.1 + xy.2 ≤ t then (1:R) else 0)
  by
    fun_trans only [scalarGradient, scalarCDeriv]
    simp only [ftrans_simp]

    rw[surfaceDirac_substitution
        (I:= Unit)
        (X₁:=fun _ => R) (X₂:= fun _ => R)
        (p:= fun _ x y => (x,y))
        (ζ:= fun b x => t' - x)
        (dom:= fun _ => Set.univ)
        (inv:= by intro i x₁ _; dsimp; simp) (hdim := sorry_proof)]

    autodiff; autodiff; norm_num

    conv in Set.preimage1 _ _ =>
      rw[Set.preimage1_prod]
      simp only [ftrans_simp]

    simp only [ftrans_simp,action_push]
    simp (disch:=sorry) only [ftrans_simp]
    rand_pull_E

𝒟'(X,𝒟'(Y,ℝ)) := L(𝒟 X, Y)


#eval Rand.print_mean_variance (foo2 0.3) 1000 ""
#eval Rand.print_mean_variance (foo2 1.7) 1000 ""


def foo3 (t' : R) :=
  derive_random_approx
    (∂ (t:=t'), ∫' (xy : R×R) in (Ioo 0 1).prod (Ioo 0 1), if xy.1 + xy.2 ≤ t then (1:R) else 0)
  by
    fun_trans only [scalarGradient, scalarCDeriv]
    simp only [ftrans_simp]

    rw[surfaceDirac_substitution
        (I:= Unit)
        (X₁:=fun _ => R) (X₂:= fun _ => R)
        (p:= fun _ x y => (x+y,y-x))
        (ζ:= fun b _ => t'/2)
        (dom:= fun _ => Set.univ)
        (inv:= by intro i x₁ _; dsimp; ring) (hdim := sorry_proof)]

    autodiff; autodiff; norm_num only [ftrans_simp]

    conv in Set.preimage1 _ _ =>
      unfold Set.preimage1
      simp only [ftrans_simp]
      fun_trans
      equals Ioo (-1) 1 => sorry

    simp only [ftrans_simp,action_push]
    simp (disch:=sorry) only [ftrans_simp]
    norm_num only [ftrans_simp]
    rand_pull_E

#eval Rand.print_mean_variance (foo3 0.3) 10000 ""
#eval Rand.print_mean_variance (foo3 1.7) 10000 ""


def foo4 (t' : R) :=
  derive_random_approx
    (∂ (t:=t'), ∫' (x : R) in Ioo 0 1, ∫' (y : R) in Ioo 0 1, if x ≤ t then x*y*t else x+y+t)
  by
    fun_trans only [scalarGradient, scalarCDeriv]
    simp only [ftrans_simp]
    simp only [Tactic.if_pull]
    fun_trans only [scalarGradient, scalarCDeriv,ftrans_simp]
    simp (disch:=sorry) only [action_push, ftrans_simp]
    rand_pull_E
    simp
