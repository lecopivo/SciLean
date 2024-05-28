import SciLean.Mathlib.Analysis.MetricSpace
import SciLean.Mathlib.Set

import SciLean.Core.Objects.Scalar

import SciLean.Tactic.GTrans
import SciLean.Tactic.IfPull

open SciLean Set

@[gtrans]
def SciLean.BoundingBall {X} [MetricSpaceP X 2]
    (A : Set X)
    (center : outParam X) (radius : outParam ℝ) : Prop :=
  A ⊂ Metric.closedBallP 2 center radius


open Set in
@[gtrans]
theorem Set.prod.bounding_ball
    {X} {Y} [MetricSpaceP X 2] [MetricSpaceP Y 2]
    (A : Set X) (B : Set Y) (cx : X) (cy : Y) (rx ry : ℝ)
    (hA : BoundingBall A cx rx) (hB : BoundingBall B cy ry) :
    BoundingBall (A ×ˢ B) (cx,cy) (rx^2 + ry^2).sqrt := sorry_proof


@[gtrans]
theorem Set.fst.bounding_ball
    {X} {Y} [MetricSpaceP X 2] [MetricSpaceP Y 2]
    (A : Set (X×Y)) (b : Y)  (center : X×Y) (radius : ℝ)
    (hA : BoundingBall A center radius) :
    let center' := center.1
    let radius' := (radius^2 - (distP 2 center.2 b)^2).sqrt
    BoundingBall (A.fst b) center' radius' := sorry_proof


@[gtrans]
theorem Set.snd.bounding_ball
    {X} {Y} [MetricSpaceP X 2] [MetricSpaceP Y 2]
    (A : Set (X×Y)) (a : X)  (center : X×Y) (radius : ℝ)
    (hA : BoundingBall A center radius) :
    let center' := center.2
    let radius' := (radius^2 - (distP 2 center.1 a)^2).sqrt
    BoundingBall (A.snd a) center' radius' := sorry_proof


@[gtrans]
theorem Set.inter.left_bounding_ball
    {X} [MetricSpaceP X 2]
    (A B : Set X) (center : X) (radius : ℝ)
    (hA : BoundingBall A center radius) :
    BoundingBall (A ∩ B) center radius := sorry_proof

@[gtrans]
theorem Set.inter.right_bounding_ball
    {X} [MetricSpaceP X 2]
    (A B : Set X) (center : X) (radius : ℝ)
    (hB : BoundingBall B center radius) :
    BoundingBall (A ∩ B) center radius := sorry_proof


variable {R} [RealScalar R]

-- TODO: make sure that we can do bounding balls on `R×R` or similar
--       I somehow need to make sure that Preorder structure is compatible with
--       the distance function

@[gtrans]
theorem Set.Icc.bounding_ball (a b : R) :
    BoundingBall (Icc a b) ((a + b)/2) (Scalar.toReal R ((b-a)/2)) := sorry_proof

@[gtrans]
theorem Set.Ioo.bounding_ball (a b : R) :
    BoundingBall (Ioo a b) ((a + b)/2) (Scalar.toReal R ((b-a)/2)) := sorry_proof

@[gtrans]
theorem Set.Ico.bounding_ball (a b : R) :
    BoundingBall (Ico a b) ((a + b)/2) (Scalar.toReal R ((b-a)/2)) := sorry_proof

@[gtrans]
theorem Set.Ioc.bounding_ball (a b : R) :
    BoundingBall (Ioc a b) ((a + b)/2) (Scalar.toReal R ((b-a)/2)) := sorry_proof
