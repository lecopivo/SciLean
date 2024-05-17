import SciLean.Core.Integral.HasDerivUnderIntegral
import SciLean.Core.Integral.RnDeriv
import SciLean.Core.Integral.Substitution
import SciLean.Core.Integral.PlaneDecomposition

open SciLean MeasureTheory Set

variable
  {R : Type} [RealScalar R] [MeasureSpace R]
  -- {W : Type} [Vec R W]
  -- {X : Type} [SemiHilbert R X] [MeasureSpace X]
  -- {Y : Type} [Vec R Y] [Module ℝ Y]
  -- {Z : Type} [Vec R Z] [Module ℝ Z]

set_default_scalar R



section Theorems

variable
  {U V W : Type}
  {S : Type} [Vec R S]
  {X : Type} [SemiHilbert R X] [MeasureSpace X]
  {Y : Type} [MeasurableSpace Y]
  [AddCommGroup U] [Module R U] [Module ℝ U] [TopologicalSpace U]
  -- [Vec R U] [Module ℝ U]
  [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]




-- -- vectorIntegral (fun x => w * x - (w + x)) (Measure.restrictToLevelSet volume (fun w x => x - w) w 1) fun y r => r * y;

open FiniteDimensional


-- WARNING: changing assumption
--          [AddCommGroup U] [Module R U] [Module ℝ U] [TopologicalSpace U]
--          to
--          [Vec R U] [Module ℝ U]
--          makes this theorem to fail unification
open BigOperators in
@[ftrans_simp]
theorem asdf (f : X → U) (d) (φ ψ : X → R)
    {I} {X₁ X₂ : I → Type}
    (p : (i : I) → X₁ i → X₂ i → X) (g : (i : I) → X₁ i → X₂ i) (dom : (i : I) → Set (X₁ i))
    (hinv : ParametricInverseAt (fun x => φ x - ψ x) 0 p g dom)
    [Fintype I] [∀ i, SemiHilbert R (X₁ i)] [∀ i, MeasureSpace (X₁ i)] :
    ∫' x in {x | φ x = ψ x}, f x ∂((surfaceMeasure d))
    =
    let sub := fun i x => p i x (g i x)
    let J := fun i x => jacobian R (sub i) x
    ∑ i : I, ∫' x, J i x • f (sub i x) := sorry_proof


end Theorems


variable (t w : R)


macro "integral_deriv" : conv =>
  `(conv| fun_trans (config:={zeta:=false}) (disch:=first | assumption | gtrans) only
      [↓ refinedRewritePre, ↑ refinedRewritePost, ftrans_simp, Tactic.lift_lets_simproc,
       scalarGradient, scalarCDeriv])

attribute [ftrans_simp] inv_one neg_sub sub_neg_eq_add

@[simp, ftrans_simp]
theorem _root_.FiniteDimensional.finrank_unit {R} [Ring R] :
    FiniteDimensional.finrank R Unit = 0 := sorry_proof


set_option pp.funBinderTypes true
set_option profiler true

set_option trace.Meta.Tactic.simp.rewrite true in
set_option trace.Meta.Tactic.simp.unify true in
set_option trace.Meta.Tactic.simp.discharge true in
-- set_option trace.Meta.Tactic.gtrans true in
-- set_option pp.funBinderTypes true in
-- set_option trace.Meta.Tactic.fun_prop true in
-- set_option trace.Meta.Tactic.gtrans.candidates true in
-- set_option trace.Meta.isDefEq true in
-- set_option trace.Meta.isDefEq.assign true in
-- set_option trace.Meta.isDefEq.stuck true in
-- set_option trace.Meta.isDefEq.stuckMVar true in
-- set_option trace.Meta.isDefEq.assign.typeError true in
-- set_option trace.Meta.isDefEq.assign.checkTypes true in
example :
    (∂ w':=w,
      ∫' x,
        if x ≤ w' then w'*x else w'+x)
    =
    sorry := by

  conv =>
    lhs
    integral_deriv

  sorry_proof



-- set_option trace.Meta.Tactic.simp.unify true in
-- set_option trace.Meta.Tactic.simp.discharge true in


set_option trace.Meta.Tactic.simp.rewrite true in
example:
    (∂ (w:=w'),
      ∫' x in Icc (0:R) 1,
        if x ≤ w then if 2*w + x ≤ 0 then 5*w*x else 2*w*w*x else w + x)
    =
    sorry := by

  conv =>
    lhs
    integral_deriv

  sorry_proof

attribute [gtrans] parametric_inverse_affine'
#check parametric_inverse_affine'

set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.gtrans true in
set_option trace.Meta.Tactic.gtrans.candidates true in


example :
    (∂ (w:=w'),
      ∫' x in Icc (0:R) 1, ∫' y in Icc (0:R) 1,
        if y ≤ w then (1:R) else 0)
    =
    sorry := by

  conv =>
    lhs
    integral_deriv

  sorry_proof


example :
    (∂ (w:=w'),
      ∫' x in Icc (0:R) 1, ∫' y in Icc (0:R) 1,
        if x + y + w ≤ 0 then (1:R) else 0)
    =
    sorry := by

  conv =>
    lhs
    integral_deriv

  sorry_proof


example :
    (∂ t:=t',
      ∫' (xy : R×R) in (Icc 0 1) ×ˢ (Icc 0 1),
        if xy.1 ≤ t then
          -if xy.2 ≤ t then (1:R) else 0
        else
          if xy.1 + xy.2 ≤ t then t else t*t)
    =
    sorry := by
  conv =>
    lhs
    integral_deriv

  sorry_proof
