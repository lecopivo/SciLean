import SciLean.Core.Integral.MovingDomain
import SciLean.Core.Integral.Substitution
import SciLean.Core.Integral.ParametricInverse
import SciLean.Core.Integral.Frontier

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

#check ∫' (x : R), x

#check (volume : Measure (R×R))

#check SciLean.frontier_inter

-- set_option trace.Meta.Tactic.simp.discharge true in
-- set_option trace.Meta.Tactic.simp.rewrite true in
-- set_option trace.Meta.Tactic.fun_trans true in
#check
  (cderiv R fun (t : R) => ∫' (x : R×R),
    if x.1^2 + x.2^2 ≤ t^2 then
      x.1
    else
      0)
  rewrite_by
    enter [t,dt]
    simp only [ftrans_simp, split_integral_of_ite]
    rw[moving_volume_derivative (f:=_) (A:=_) (hA:=sorry)]
    fun_trans [ftrans_simp]
    rw[intetgral_parametric_inverse (R:=R) (Y:=R) (I:=Unit) (X₁ := fun _ => R) (f:=_) (d:=1) (hdim:=sorry) (inv:=circle_polar_inverse (t^2) sorry)]
    unfold scalarGradient
    fun_trans only [scalarGradient,ftrans_simp]
    simp only [Finset.univ_unique, PUnit.default_eq_unit, ftrans_simp, Finset.sum_const, Finset.card_singleton]

    -- simp only [Finset.univ_unique, PUnit.default_eq_unit, smul_eq_mul, Finset.sum_const, Finset.card_singleton, one_smul]

#check Nat

#check circle_polar_inverse

open BigOperators in
#check
  (cderiv R fun (t : R) => ∫' (x : R×R),
    if x.1^2 + x.2^2 ≤ t^2 then
      x.1
    else
      0)
  rewrite_by
    enter [t,dt]
    simp only [ftrans_simp]
    rw[moving_volume_derivative (f:=_) (A:=_) (hA:=sorry)]
    fun_trans [ftrans_simp,scalarGradient]
    rw[intetgral_parametric_inverse (R:=R) (hdim:=sorry) (inv:=circle_sqrt_inverse (t^2) sorry)]
    simp only [scalarGradient,ftrans_simp]
    simp only [Finset.univ_unique, PUnit.default_eq_unit, ftrans_simp, Finset.sum_const, Finset.card_singleton]
