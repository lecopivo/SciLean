import SciLean.Core.Integral.HasParamDerivWithJumps
import SciLean.Core.Integral.HasParamFwdDerivWithJumps
import SciLean.Core.Integral.HasParamRevDerivWithJumps
import SciLean.Core.Integral.HasParamDerivWithJumpsCommon
import SciLean.Tactic.LSimp
import SciLean.Tactic.LFunTrans
import SciLean.Core.Integral.SurfaceIntegral

open SciLean MeasureTheory Set

variable
  {R : Type} [RealScalar R] [MeasureSpace R] [BorelSpace R] [PlainDataType R]

set_default_scalar R

-- set_option trace.Meta.Tactic.simp.discharge true
-- set_option trace.Meta.Tactic.simp.unify true

-- set_option trace.Meta.Tactic.gtrans true
-- set_option trace.Meta.Tactic.gtrans.arg true

-- @[ftrans_simp]
-- theorem asdf
--   {X} [NormedAddCommGroup X] [AdjointSpace ℝ X] [AdjointSpace R X]
--   {Y} [NormedAddCommGroup Y] [AdjointSpace ℝ Y] [AdjointSpace R Y]
--   (f : X → Y) (x : X) :
--   Scalar.ofReal R (jacobian ℝ f x) = jacobian R f x := sorry_proof

example (w : R) (a b c d : R) :
    (fderiv R (fun w' =>
      ∫ xy in Icc (0:R) 1 |>.prod (Icc (0 : R) 1),
        if a * xy.1 + b * xy.2 + c ≤ d * w' then (1:R) else 0) w 1)
    =
    sorry := by

  conv =>
    lhs

    rw[fderiv_under_integral_over_set
           (hf:= by gtrans
                      (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
                      (norm:=lsimp only [ftrans_simp]))
                      (hA := by assume_almost_disjoint)]

    lautodiff (disch:=fun_prop)

    lsimp (config:={singlePass:=true}) (disch:=gtrans (disch:=fun_prop)) only
      [surface_integral_parametrization_inter'',ftrans_simp]

    lautodiff
