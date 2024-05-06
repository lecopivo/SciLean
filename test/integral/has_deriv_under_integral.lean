import SciLean.Core.Integral.HasDerivUnderIntegral
import SciLean.Core.Integral.RnDeriv

open SciLean MeasureTheory Set

variable
  {R : Type} [RealScalar R] [MeasureSpace R]
  -- {W : Type} [Vec R W]
  -- {X : Type} [SemiHilbert R X] [MeasureSpace X]
  -- {Y : Type} [Vec R Y] [Module ℝ Y]
  -- {Z : Type} [Vec R Z] [Module ℝ Z]

set_default_scalar R


variable (t w : R)


macro "integral_deriv" : conv =>
  `(conv| fun_trans (config:={zeta:=false}) (disch:=first | assumption | gtrans) only
      [↓ refinedRewritePre, ↑ refinedRewritePost, ftrans_simp, Tactic.lift_lets_simproc,
       scalarGradient, scalarCDeriv])


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


example:
    (∂ (w:=w'),
      ∫' x in Icc (0:R) 1,
        if x ≤ w then if 2*w + 3*x ≤ 0 then 5*w*x else 2*w*w*x else w + x)
    =
    sorry := by

  conv =>
    lhs
    integral_deriv

  sorry_proof


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
