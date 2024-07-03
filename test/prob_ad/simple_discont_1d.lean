import SciLean.Core.Integral.HasParamDerivWithJumps
import SciLean.Core.Integral.HasParamFwdDerivWithJumps
import SciLean.Core.Integral.HasParamRevDerivWithJumps
import SciLean.Core.Integral.HasParamDerivWithJumpsCommon
import SciLean.Tactic.LSimp
import SciLean.Tactic.LFunTrans

open SciLean MeasureTheory Set

variable
  {R : Type} [RealScalar R] [MeasureSpace R] [BorelSpace R]

set_default_scalar R

-- example (w : R) :
--     (∂ w':=w,
--       ∫' x in Icc (0:R) 1,
--         if x ≤ w' then (1:R) else 0)
--     =
--     if 0 ≤ w ∧ w ≤ 1 then 1 else 0 := by

--   conv =>
--     lhs
--     integral_deriv

-- set_option trace.Meta.Tactic.simp.rewrite true


example (w : R) :
    (fderiv R (fun w' =>
      ∫ x in Icc (0:R) 1,
        if x ≤ w' then (1:R) else 0) w 1)
    =
    if w ∈ Set.Icc 0 1 then 1 else 0 := by

  conv =>
    lhs
    rw[fderiv_under_integral_over_set
           (hf:= by gtrans
                      (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
                      (norm:=lsimp only [ftrans_simp]))
                      (hA := by assume_almost_disjoint)]

    lautodiff (disch:=fun_prop)
