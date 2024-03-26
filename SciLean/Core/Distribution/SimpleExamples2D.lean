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
  {R} [RealScalar R] [MeasureSpace R]
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
  mem_ite_empty_right


open Classical
@[simp, ftrans_simp]
theorem hoho {α β γ} (f : α → β) (c : γ) (B : Set β) (C : Set γ) :
  (fun x => (f x, c)) ⁻¹' (B.prod C) = if c ∈ C then f ⁻¹' B else ∅ := sorry_proof


@[simp, ftrans_simp]
theorem hoho' {α β γ} (f : α → β) (c : γ) (B : Set β) (C : Set γ) :
  (fun x => (c, f x)) ⁻¹' (C.prod B) = if c ∈ C then f ⁻¹' B else ∅ := sorry_proof

-- set_option trace.Meta.Tactic.simp.unify true in
-- set_option trace.Meta.Tactic.simp.discharge true in
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


#eval Rand.print_mean_variance (foo1 0.3) 100 ""

@[simp, ftrans_simp]
theorem asdf (n : ℕ) : Scalar.abs (n : R) = (n : R) := sorry_proof

@[simp, ftrans_simp]
theorem asdf' : Scalar.abs (2 : R) = (2 : R) := sorry_proof


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

    conv in Set.preimage _ _ =>
      rw[hoho']
      simp only [ftrans_simp]

    conv in Set.preimage1 _ _ =>
      rw[Set.preimage1_prod]
      simp only [ftrans_simp]

    simp only [ftrans_simp,action_push,hoho,hoho']
    simp (disch:=sorry) only [ftrans_simp]
    rand_pull_E


#eval Rand.print_mean_variance (foo2 0.3) 1000 ""
#eval Rand.print_mean_variance (foo2 1.7) 1000 ""
