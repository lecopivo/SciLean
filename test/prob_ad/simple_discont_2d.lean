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


example (w : R) :
    (fderiv R (fun w' =>
      ∫ xy in Icc (0:R) 1 |>.prod (Icc (0 : R) 1),
        if xy.1 + xy.2 ≤ w' then xy.1*xy.2*w' else xy.1+xy.2+w') w 1)
    =
    sorry := by

  conv =>
    lhs

    rw[fderiv_under_integral_over_set
           (hf:= by gtrans
                      (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
                      (norm:=lsimp only [ftrans_simp]))
                      (hA := by assume_almost_disjoint)]

    lautodiff (disch:=first | fun_prop | gtrans (disch:=fun_prop))

    conv in (∫ x in _, _ ∂μH[_]) =>

      lsimp (disch:=gtrans (disch:=fun_prop)) only
        [surface_integral_parametrization_inter R]
      lautodiff (disch:=gtrans (disch:=fun_prop))
        [integral_over_bounding_ball (R:=R)]

    lsimp only

  sorry_proof
