-- import SciLean.Mathlib.Analysis.MetricSpace
import SciLean.Mathlib.Analysis.AdjointSpace.Basic
import SciLean.Mathlib.Set

import SciLean.Core.Objects.Scalar
import SciLean.Core.Objects.SemiInnerProductSpace


import SciLean.Tactic.GTrans
import SciLean.Tactic.IfPull

open SciLean Set


variable
  {R} [RealScalar R]
  {X} [NormedAddCommGroup X] [AdjointSpace R X]
  {Y} [NormedAddCommGroup Y] [AdjointSpace R Y]

set_default_scalar R

/-- Closed ball using standard Euclidean metric.

Similar to `Metric.closedBall` but uses norm originating from inner produce. Note that `ℝ×ℝ` uses
max norm therefore for `x : ℝ×ℝ` the `Metric.ball x r` is is square rather then a ball.   -/
def SciLean.closedBall₂ {X} [NormedAddCommGroup X] [AdjointSpace R X]
  (x : X) (r : R) := {y | ⟪y - x, y - x⟫_R ≤ r^2}

variable (R)
/--
`BoundaingBall₂ A c r` says that the set `A` is a subset of ball with center `c` and radius `r` -/
@[gtrans]
def SciLean.BoundingBall₂ {X} [NormedAddCommGroup X] [AdjointSpace R X]
    (A : Set X) (center : outParam X) (radius : outParam R) : Prop :=
  A ⊂ closedBall₂ center radius
variable {R}

open Scalar
open Set in
@[gtrans]
theorem Set.prod.bounding_ball
    (A : Set X) (B : Set Y) (cx : X) (cy : Y) (rx ry : R)
    (hA : BoundingBall₂ R A cx rx) (hB : BoundingBall₂ R B cy ry) :
    BoundingBall₂ R (A.prod B) (cx,cy) (sqrt (rx^2 + ry^2)) := sorry_proof


@[gtrans]
theorem SProd.sprod.bounding_ball
    (A : Set X) (B : Set Y) (cx : X) (cy : Y) (rx ry : R)
    (hA : BoundingBall₂ R A cx rx) (hB : BoundingBall₂ R B cy ry) :
    BoundingBall₂ R (A ×ˢ B) (cx,cy) (sqrt (rx^2 + ry^2)) := sorry_proof


@[gtrans]
theorem Set.fst.bounding_ball
    (A : Set (X×Y)) (b : Y) (center : X×Y) (radius : R)
    (hA : BoundingBall₂ R A center radius) :
    let center' := center.1
    let radius' := sqrt (radius^2 - ‖center.2 - b‖₂²)
    BoundingBall₂ R (A.fst b) center' radius' := sorry_proof


@[gtrans]
theorem Set.snd.bounding_ball
    (A : Set (X×Y)) (a : X) (center : X×Y) (radius : R)
    (hA : BoundingBall₂ R A center radius) :
    BoundingBall₂ R (A.snd a)
      (let center := center
       center.2)
      (let center := center
       sqrt (radius^2 - ‖center.1 - a‖₂²)) := sorry_proof


@[gtrans]
theorem Set.inter.left_bounding_ball
    (A B : Set X) (center : X) (radius : R)
    (hA : BoundingBall₂ R A center radius) :
    BoundingBall₂ R (A ∩ B) center radius := sorry_proof

@[gtrans]
theorem Set.inter.right_bounding_ball
    (A B : Set X) (center : X) (radius : R)
    (hB : BoundingBall₂ R B center radius) :
    BoundingBall₂ R (A ∩ B) center radius := sorry_proof

-- TODO: make sure that we can do bounding balls on `R×R` or similar
--       I somehow need to make sure that Preorder structure is compatible with
--       the distance function

@[gtrans]
theorem Set.Icc.bounding_ball (a b : R) :
    BoundingBall₂ R (Icc a b) ((a + b)/2) ((b-a)/2) := sorry_proof

@[gtrans]
theorem Set.Ioo.bounding_ball (a b : R) :
    BoundingBall₂ R (Ioo a b) ((a + b)/2) ((b-a)/2) := sorry_proof

@[gtrans]
theorem Set.Ico.bounding_ball (a b : R) :
    BoundingBall₂ R (Ico a b) ((a + b)/2) ((b-a)/2) := sorry_proof

@[gtrans]
theorem Set.Ioc.bounding_ball (a b : R) :
    BoundingBall₂ R (Ioc a b) ((a + b)/2) ((b-a)/2) := sorry_proof
