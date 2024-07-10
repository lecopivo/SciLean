import SciLean.Core.Transformations.HasParamDerivWithJumps.Common
import SciLean.Core.Transformations.SurfaceParametrization
import SciLean.Core.LinearAlgebra.GramSchmidt.Properties
import SciLean.Core.Rand.Distributions.Uniform
import SciLean.Core.Rand.Tactic
import SciLean.Data.DataArray
import SciLean.Tactic.Autodiff

open SciLean MeasureTheory Set Scalar

variable
  {R : Type} [RealScalar R] [MeasureSpace R] [BorelSpace R] [PlainDataType R]

set_default_scalar R

set_option trace.Meta.Tactic.simp.discharge true
set_option trace.Meta.Tactic.gtrans true
set_option trace.Meta.Tactic.gtrans.candidates true

example (w : R) :
    (fderiv R (fun w' =>
      ∫ xy in Icc (0:R) 1 ×ˢ (Icc (0 : R) 1),
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

    conv in (∫ _ in _, _ ∂μH[_]) =>

      lautodiff (disch:=gtrans (disch:=fun_prop))
        [surface_integral_parametrization_inter R,
         integral_over_bounding_ball (R:=R)]


    conv in (occs:=*) (∫ x in _, _ ∂_) =>
      . lsimp only [Rand.integral_eq_uniform_E R]
      . lsimp only [Rand.integral_eq_uniform_E R]


  sorry_proof

#check Set.snd

example (w : R) :
    (fwdFDeriv R (fun w' =>
      ∫ xy in Icc (0:R) 1 ×ˢ (Icc (0 : R) 1),
        if xy.1 + xy.2 ≤ w' then xy.1*xy.2*w' else xy.1+xy.2+w') w 1)
    =
    let interior :=
      ∫ (x : R × R) in Icc 0 1 ×ˢ Icc 0 1,
        let ydy := x.1 * x.2;
        if x.1 + x.2 ≤ w then (ydy * w, ydy) else (x.1 + x.2 + w, 1);
    let dec := hyperplaneDecomposition (1, 1);
    let a := w / Scalar.sqrt 2;
    let center := dec.symm (1 / 2, 1 / 2);
    let s :=
      ∫ (x : R^[1]) in closedBall₂ center.2 (sqrt (sqrt (1 / 2) ^ 2 - (center.1 - a) ^ 2)),
        let x_1 := dec (a, x);
        let vals := x_1.1 * x_1.2 * w;
        let vals_1 := x_1.1 + x_1.2 + w;
        if dec (a, x) ∈ Icc 0 1 ×ˢ Icc 0 1 then (sqrt (2:R))⁻¹ * (vals - vals_1) else 0;
    (interior.1, interior.2 + s) := by

  conv =>
    lhs

    rw[fwdFDeriv_under_integral_over_set
           (hf:= by gtrans
                      (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
                      (norm:=lsimp only [ftrans_simp]))
                      (hA := by assume_almost_disjoint)]

    lautodiff (disch:=first | fun_prop | gtrans (disch:=fun_prop))

    conv in (∫ _ in _, _ ∂μH[_]) =>
      lautodiff (disch:=gtrans (disch:=fun_prop))
        [surface_integral_parametrization_inter R,
         integral_over_bounding_ball (R:=R)]

    conv in (occs:=*) (∫ _ in _, _ ∂_) =>
      . lsimp only [Rand.integral_eq_uniform_E R,
                    Rand.E_eq_mean_estimateE R 10]
      . lsimp only [Rand.integral_eq_uniform_E R,
                    Rand.E_eq_mean_estimateE R 10]

    lsimp only
  sorry_proof


open Scalar

example (w : R) :
    (fgradient (fun w' =>
      ∫ xy in Icc (0:R) 1 ×ˢ (Icc (0 : R) 1),
        if xy.1 + xy.2 ≤ w' then xy.1*xy.2*w' else xy.1+xy.2+w') w)
    =
    let interior :=
      ∫ (x : R × R) in Icc 0 1 ×ˢ Icc 0 1,
        let ydf := x.1 * x.2;
        if x.1 + x.2 ≤ w then ydf else 1;
    let dec := hyperplaneDecomposition (1, 1);
    let a := w / Scalar.sqrt 2;
    let center := dec.symm (1 / 2, 1 / 2);
    let s :=
      ∫ (x : R^[1]) in closedBall₂ center.2 (sqrt (sqrt (1 / 2) ^ 2 - (center.1 - a) ^ 2)),
        let x_1 := dec (a, x);
        let vals := x_1.1 * x_1.2 * w;
        let vals_1 := x_1.1 + x_1.2 + w;
        if dec (a, x) ∈ Icc 0 1 ×ˢ Icc 0 1 then
          (vals - vals_1) * (sqrt (2:R))⁻¹
        else 0;
    interior + s := by

  conv =>
    lhs

    -- run AD
    unfold fgradient
    rw[revFDeriv_under_integral_over_set
           (hf:= by gtrans
                      (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
                      (norm:=lsimp only [ftrans_simp]))
                      (hA := by assume_almost_disjoint)]

    lautodiff (disch:=first | fun_prop | gtrans (disch:=fun_prop)) [frontierGrad]

    -- deal with surface integrals
    conv in (∫ _ in _, _ ∂μH[_]) =>
      lautodiff (disch:=gtrans (disch:=fun_prop))
        [surface_integral_parametrization_inter R,
         integral_over_bounding_ball (R:=R)]

    -- turn integrals into expectations
    conv in (occs:=*) (∫ _ in _, _ ∂_) =>
      . lsimp only [Rand.integral_eq_uniform_E R]
      . lsimp only [Rand.integral_eq_uniform_E R]

  sorry_proof
