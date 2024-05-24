import SciLean.Core.Integral.Common
import SciLean.Core.Integral.BoundingBall
import SciLean.Tactic.IfPull
import SciLean.Util.Profile

open SciLean MeasureTheory Set

variable
  {R : Type} [RealScalar R] [MeasureSpace R] [PlainDataType R]

set_default_scalar R

open Classical in
theorem cintegral_boundinb_ball_domain
    {X} [MeasureSpace X] [MetricSpaceP X 2]
    {U} [AddCommGroup U] [Module ℝ U]
    (A : Set X) (f : X → U)
    (center : X) (radius : ℝ) (hball : BoundingBall A center radius) :
    ∫' y in A, f y
    =
    ∫' x in Metric.closedBallP 2 center radius, (if x ∈ A then f x else 0) := sorry


open IndexType in
@[gtrans]
theorem planeDecomposition_bounding_ball
    {n} {ι} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι] {X} [FinVec ι R X] [MetricSpaceP X 2]
    (u : X) (hn : n + 1 = card ι := by first | assumption | infer_var)
    (A : Set X) (center : X) (radius : ℝ)
    (hA : BoundingBall A center radius) :
    let center' := ((planeDecomposition (R:=R) u hn).symm center)
    BoundingBall ((fun x => planeDecomposition u hn x) ⁻¹' A) center' radius := sorry


-- @[simp, ftrans_simp]
-- theorem invFun_equiv [Nonempty α] (f : α ≃ β) :
--   Function.invFun f = f.symm := sorry_proof

set_option profiler true
-- set_option trace.Meta.Tactic.fun_trans true
-- set_option trace.Meta.Tactic.fun_prop true
-- set_option trace.Meta.Tactic.gtrans true
-- set_option trace.Meta.Tactic.gtrans.arg true


@[simp, ftrans_simp]
theorem dist_sqrt (x y : ℝ) : (x^2 + y^2).sqrt^2 = x^2 + y^2 := sorry_proof


example (w : R) (a b c d : R) :
    (∂ w':=w,
      ∫' x in Icc (0:R) 1, ∫' y in Icc (0:R) 1,
        if a * x + b * y + c ≤ d * w' then (1:R) else 0)
    =
    sorry := by

  conv =>
    integral_deriv
    simp (config := {zeta:=false}) (disch:=gtrans) only [cintegral_boundinb_ball_domain]
    integral_deriv

  sorry_proof




#exit
/--
info: let ds :=
  ∫' x,
    jacobian R (fun x => (planeDecomposition (a, b) ⋯) ((d * w - c) / Scalar.sqrt (a ^ 2 + b ^ 2), x)) x *
      ((Scalar.sqrt (a ^ 2 + b ^ 2))⁻¹ *
        d) ∂volume.restrict
      (((fun x12 => (planeDecomposition (a, b) ⋯) x12) ⁻¹' Icc 0 1 ×ˢ Icc 0 1).snd
        ((d * w - c) / Scalar.sqrt (a ^ 2 + b ^ 2)));
ds : R
-/
#guard_msgs in
#check (∂ w':=w,
      ∫' x in Icc (0:R) 1, ∫' y in Icc (0:R) 1,
        if a * x + b * y + c ≤ d * w' then (1:R) else 0) rewrite_by integral_deriv; autodiff
