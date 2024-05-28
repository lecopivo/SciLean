import SciLean.Core.Integral.Common
import SciLean.Core.Integral.BoundingBall
import SciLean.Tactic.IfPull
import SciLean.Util.Profile

open SciLean MeasureTheory Set

variable
  {R : Type} [RealScalar R] [MeasureSpace R] [PlainDataType R]

set_default_scalar R


-- set_option profiler true
-- set_option trace.Meta.Tactic.fun_trans true
-- set_option trace.Meta.Tactic.fun_trans.rewrite true
-- set_option trace.Meta.Tactic.fun_prop true
-- set_option trace.Meta.Tactic.gtrans true
-- set_option trace.Meta.Tactic.gtrans.arg true
-- set_option trace.Meta.Tactic.simp.rewrite true
-- set_option trace.Meta.Tactic.simp.discharge true

example (w : R) (a b c d : R) :
    (∂ w':=w,
      ∫' x in Icc (0:R) 1, ∫' y in Icc (0:R) 1,
        if a * x + b * y + c ≤ d * w' then (1:R) else 0)
    =
    sorry := by
    -- let dec := planeDecomposition (R:=R) (a, b)
    -- let r := Scalar.sqrt (a ^ 2 + b ^ 2)
    -- let ds :=
    --   ∫' x,
    --     if
    --         (0 ≤ (dec ((d * w - c) / r, x)).1 ∧
    --             (dec ((d * w - c) / r, x)).1 ≤ 1) ∧
    --           0 ≤ (dec ((d * w - c) / r, x)).2 ∧
    --             (dec ((d * w - c) / r, x)).2 ≤ 1 then
    --       Inv.inv r * d
    --     else
    --       0 ∂volume.restrict
    --       (Metric.closedBallP 2 (dec.symm (1/2, 1/2)).2
    --         √(Scalar.toReal R (1/2) ^ 2 + Scalar.toReal R (1/2) ^ 2 - distP 2 (dec.symm (1/2, 1/2)).1 ((d * w - c) / r) ^ 2));
    -- ds := by

  conv =>
    lhs
    -- there is an issue with `first | assumption | ...` discharger for `gtrans`
    -- simp
    --   (config := {zeta:=false})
    --   (disch:=first | assumption | (gtrans (disch:=first | assumption | (fun_prop (disch:=assumption))))) only
    --   [ftrans_simp,ftrans_simp, Tactic.lift_lets_simproc, scalarGradient, scalarCDeriv]

    fun_trans
      (config := {zeta:=false})
      (disch:=first | assumption | (gtrans (disch:=(fun_prop (disch:=assumption)))))
      only [ftrans_simp,ftrans_simp, Tactic.lift_lets_simproc, scalarGradient, scalarCDeriv]

    simp
      (config := {zeta:=false,singlePass:=true})
      (disch:=gtrans)
      only [cintegral_bound_domain_ball]

    autodiff

  sorry_proof
