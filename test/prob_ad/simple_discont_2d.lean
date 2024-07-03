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

set_option trace.Meta.Tactic.simp.discharge true
set_option trace.Meta.Tactic.simp.unify true

set_option trace.Meta.Tactic.gtrans true
set_option trace.Meta.Tactic.gtrans.arg true


#synth NormedAddCommGroup (SciLean.DataArrayN R (Fin 1))

example (w : R) :
    (fderiv R (fun w' =>
      ∫ xy in Icc (0:R) 1 |>.prod (Icc (0 : R) 1),
        if xy.1 + xy.2 ≤ w' then (1:R) else 0) w 1)
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

    lsimp (disch:=gtrans (disch:=fun_prop)) only [surface_integral_parametrization_inter',ftrans_simp]

    lautodiff

    lautodiff

    -- fun_trans
    --   (config := {zeta:=false})
    --   (disch:=first | assumption | (gtrans (disch:=(fun_prop (disch:=assumption)))))
    --   only [ftrans_simp,ftrans_simp, Tactic.lift_lets_simproc, scalarGradient, scalarCDeriv]

    -- simp
    --   (config := {zeta:=false,singlePass:=true})
    --   (disch:=gtrans)
    --   only [cintegral_bound_domain_ball]

    -- autodiff

  sorry_proof



#check_simp (1 + 1 : ℝ) ~> (2 : ℝ)

#check univ_inter



#synth NormedAddCommGroup (R^[2])
#synth NormedSpace R (R^[2])
#synth NormedSpace ℝ (R^[2])
