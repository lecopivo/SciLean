import SciLean.Core.Integral.HasParamDerivWithJumps
import SciLean.Core.Integral.HasParamFwdDerivWithJumps
import SciLean.Core.Integral.HasParamRevDerivWithJumps
import SciLean.Core.Integral.HasParamDerivWithJumpsCommon
import SciLean.Tactic.LSimp
import SciLean.Tactic.LFunTrans
import SciLean.Core.Integral.SurfaceIntegral

open SciLean MeasureTheory Set Scalar

variable
  {R : Type} [RealScalar R] [MeasureSpace R] [BorelSpace R] [PlainDataType R]

set_default_scalar R


example (w : R) (a b c d : R) :
    (fderiv R (fun w' =>
      ∫ xy in Icc (0:R) 1 ×ˢ (Icc (0 : R) 1),
        if a * xy.1 + b * xy.2 + c ≤ d * w' then xy.1*xy.2*w'*w' else 0) w 1)
    =
    let interior :=
      ∫ (x : R × R) in Icc 0 1 ×ˢ Icc 0 1,
        let fx := x.1 * x.2 * w;
        let fx_1 := x.1 * x.2;
        if a * x.1 + b * x.2 + c ≤ d * w then fx + fx_1 * w else 0;
    let dec := planeDecomposition (a, b);
    let a_1 := (d * w - c) / Scalar.sqrt (a ^ 2 + b ^ 2);
    let center := dec.symm (1 / 2, 1 / 2);
    let s :=
      ∫ (x : R^[1]) in closedBall₂ center.2 (sqrt (sqrt (1 / 2) ^ 2 - (center.1 - a_1) ^ 2)),
        let x_1 := dec (a_1, x);
        let vals := x_1.1 * x_1.2 * w * w;
        if dec (a_1, x) ∈ Icc 0 1 ×ˢ Icc 0 1 then d / sqrt (a ^ 2 + b ^ 2) * vals else 0;
    interior + s := by

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



example (w : R) (a b c d : R) :
    (fgradient (fun w' =>
      ∫ xy in Icc (0:R) 1 ×ˢ (Icc (0 : R) 1),
        if a * xy.1 + b * xy.2 + c ≤ d * w' then xy.1*xy.2*w'*w' else 0) w)
    =
    let interior :=
       ∫ (x : R × R) in Icc 0 1 ×ˢ Icc 0 1,
         let ydf := x.1 * x.2;
         let ydf_1 := ydf * w;
         if a * x.1 + b * x.2 + c ≤ d * w then w * ydf + ydf_1 else 0;
     let dec := planeDecomposition (a, b);
     let a_1 := (d * w - c) / Scalar.sqrt (a ^ 2 + b ^ 2);
     let center := dec.symm (1 / 2, 1 / 2);
     let s :=
       ∫ (x : R^[1]) in closedBall₂ center.2 (sqrt (sqrt (1 / 2) ^ 2 - (center.1 - a_1) ^ 2)),
         let x_1 := dec (a_1, x);
         let vals := x_1.1 * x_1.2 * w * w;
         if dec (a_1, x) ∈ Icc 0 1 ×ˢ Icc 0 1 then vals * ((Scalar.sqrt (a ^ 2 + b ^ 2))⁻¹ * d)
         else 0;
     interior + s := by

  conv =>
    lhs
    unfold fgradient
    rw[revFDeriv_under_integral_over_set
           (hf:= by gtrans
                      (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
                      (norm:=lsimp only [ftrans_simp]))
                      (hA := by assume_almost_disjoint)]

    lautodiff (disch:=first | fun_prop | gtrans (disch:=fun_prop)) [frontierGrad]

    conv in (∫ x in _, _ ∂μH[_]) =>

      lsimp (disch:=gtrans (disch:=fun_prop)) only
        [surface_integral_parametrization_inter R]
      lautodiff (disch:=gtrans (disch:=fun_prop))
        [integral_over_bounding_ball (R:=R)]

    lsimp only
