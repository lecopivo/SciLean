import SciLean.Core.Integral.Common
import SciLean.Core.Integral.BoundingBall
import SciLean.Tactic.IfPull

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
    ∫' x in Metric.pclosedBall 2 center radius, (if x ∈ A then f x else 0) := sorry



open IndexType in
@[gtrans]
theorem planeDecomposition_bounding_ball
    {n} {ι} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι] {X} [FinVec ι R X] [MetricSpaceP X 2]
    (u : X) (hn : n + 1 = card ι := by first | assumption | infer_var)
    (A : Set X) (center : X) (radius : ℝ)
    (hA : BoundingBall A center radius) :
    let center' := ((planeDecomposition (R:=R) u hn).symm center)
    BoundingBall ((fun x => planeDecomposition u hn x) ⁻¹' A) center' radius := sorry

-- BoundingBall ((fun x12 => (planeDecomposition (a, b) ⋯) x12) ⁻¹' Icc 0 1 ×ˢ Icc 0 1) ?center ?radius

@[simp, ftrans_simp]
theorem indicator_of_preimage {α β M} [Zero M] (f : α → β) (m : M) (B : Set β) (x : α) :
  (f ⁻¹' B).indicator (fun _ => m) x
  =
  B.indicator (fun _ => m) (f x) := by rfl


@[simp, ftrans_simp]
theorem indicator_of_preimage' {α β M} [Nonempty α] [Zero M] (f : α → β) (g : α → M) (B : Set β) (x : α) :
  (f ⁻¹' B).indicator g x
  =
  B.indicator (fun y => g (f.invFun y)) (f x) := sorry_proof


@[simp, ftrans_simp]
theorem invFun_equiv [Nonempty α] (f : α ≃ β) :
  Function.invFun f = f.symm := sorry_proof

open Classical in
@[simp, ftrans_simp]
theorem indicator_of_snd {α β M} [Zero M] (A : Set (α×β)) (m : M)  (a : α) (y : β) :
    (A.snd a).indicator (fun _ => m) y
    =
    if (a,y) ∈ A then m else 0 := by
  unfold Set.indicator Set.snd
  if h : (a, y) ∈ A then simp[h] else simp[h]

set_option trace.Meta.Tactic.gtrans true
set_option trace.Meta.Tactic.gtrans.arg true
set_option trace.Meta.Tactic.simp.rewrite true
set_option trace.Meta.Tactic.simp.unify true
set_option trace.Meta.Tactic.simp.discharge true


@[simp, ftrans_simp]
theorem dist_sqrt (x y : ℝ) : (x^2 + y^2).sqrt^2 = x^2 + y^2 := sorry_proof

example (w : R) (a b c d : R) :
    (∂ w':=w,
      ∫' x in Icc (0:R) 1, ∫' y in Icc (0:R) 1,
        if a * x + b * y + c ≤ d * w' then (1:R) else 0)
    =
    sorry := by

  conv =>
    lhs
    integral_deriv
    simp (config := {zeta:=false}) (disch:=gtrans) only [cintegral_boundinb_ball_domain]
    integral_deriv
    simp (config:={zeta:=false})

  sorry_proof



variable (w : R) (a b c d : R)




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
