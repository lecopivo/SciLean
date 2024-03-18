import SciLean.Core.Integral.MovingDomain
import SciLean.Core.Integral.Substitution
import SciLean.Core.Integral.ParametricInverse
import SciLean.Core.Integral.Frontier
import SciLean.Core.Functions.Trigonometric

open MeasureTheory

namespace SciLean

variable
  {R} [RealScalar R]
  {W} [SemiHilbert R W]
  {X} [SemiHilbert R X]
  {Y} [SemiHilbert R Y] [Module ℝ Y]
  {Z} [SemiHilbert R Z] [Module ℝ Z]

set_default_scalar R

variable [MeasureSpace R] [Module ℝ R]

attribute [ftrans_simp] FiniteDimensional.finrank_prod FiniteDimensional.finrank_self Finset.univ_unique Finset.sum_const Finset.card_singleton Prod.smul_mk -- Nat.reduceAdd

@[simp, ftrans_simp]
theorem Scalar.sqrt_pow (r : R) : Scalar.sqrt (r^2) = Scalar.abs r := sorry_proof

@[simp, ftrans_simp]
theorem Scalar.abs_abs (r : R) : Scalar.abs (Scalar.abs r) = Scalar.abs r := sorry_proof

--  Nat.succ_sub_succ_eq_sub, tsub_zero]
-- SciLean.HasAdjDiff R fun x => (SciLean.Scalar.cos x, SciLean.Scalar.sin x)

-- set_option trace.Meta.Tactic.simp.discharge true in
-- set_option trace.Meta.Tactic.simp.rewrite true in
set_option trace.Meta.Tactic.fun_trans true in
#check
  (cderiv R fun (t : R) => ∫' (x : R×R),
    if x.1^2 + x.2^2 ≤ t^2 then
      x.1
    else
      0)
  rewrite_by
    enter [t,dt]
    fun_trans (disch:=sorry) only [ftrans_simp,scalarGradient]
    rw[intetgral_parametric_inverse (R:=R) (hdim:=sorry) (inv:=circle_polar_inverse (t^2) sorry)]
    fun_trans only [ftrans_simp]



open BigOperators in
set_option trace.Meta.Tactic.fun_trans true in
#check
  (cderiv R fun (t : R) => ∫' (x : R×R),
    if x.1^2 + x.2^2 ≤ t^2 then
      x.1
    else
      0)
  rewrite_by
    enter [t,dt]
    fun_trans (disch:=sorry) only [ftrans_simp,scalarGradient]
    rw[intetgral_parametric_inverse (R:=R) (hdim:=sorry) (inv:=circle_sqrt_inverse (t^2) sorry)]
    fun_trans (disch:=sorry) only [ftrans_simp,scalarGradient]
