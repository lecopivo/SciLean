import SciLean.Core.Integral.Common
import SciLean.Tactic.IfPull

open SciLean MeasureTheory Set

variable
  {R : Type} [RealScalar R] [MeasureSpace R] [PlainDataType R]

set_default_scalar R


example (w : R) :
    (∂ w':=w,
      ∫' x in Icc (0:R) 1, ∫' y in Icc (0:R) 1,
        if x + y ≤ w' then (1:R) else 0)
    =
    sorry := by

  conv =>
    lhs

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
