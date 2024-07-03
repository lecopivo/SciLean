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


-- set_option trace.Meta.Tactic.fun_trans true in
-- set_option trace.Meta.Tactic.fun_prop true in

example (w : R) (a b c : R) (ha : a ≠ 0) :
    (fderiv R (fun w' =>
      ∫ x in Icc (0:R) 1,
        if a * x + b ≤ c * w' then (1:R) else 0) w 1)
    =
    let x' := a⁻¹ * (c * w - b);
    if x' ∈ Icc 0 1 then
      c / (Scalar.abs a)
    else 0 := by

  conv =>
    lhs
    rw[fderiv_under_integral_over_set
           (hf:= by gtrans
                      (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
                      (norm:=lsimp only [ftrans_simp]))
                      (hA := by assume_almost_disjoint)]

    lautodiff (disch:=first | assumption | fun_prop (disch:=assumption))
