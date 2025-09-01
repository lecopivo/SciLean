import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

import SciLean.Analysis.AdjointSpace.Basic
import SciLean.Analysis.AdjointSpace.Geometry
import SciLean.Analysis.Scalar
import SciLean.Logic.Function.Preimage

import SciLean.Tactic.GTrans

open SciLean Set MeasureTheory

variable
  {R} [RealScalar R]
  {X} [NormedAddCommGroup X] [AdjointSpace R X]
  {Y} [NormedAddCommGroup Y] [AdjointSpace R Y]

set_default_scalar R


variable (R)
/--
`BoundaingBall₂ A c r` says that the set `A` is a subset of ball with center `c` and radius `r` -/
@[gtrans]
def SciLean.BoundingBall₂ {X} [NormedAddCommGroup X] [AdjointSpace R X]
    (A : Set X) (center : outParam X) (radius : outParam R) : Prop :=
  A ⊂ closedBall₂ center radius
variable {R}



----------------------------------------------------------------------------------------------------

section IntegralOverBoundingBall
set_option deprecated.oldSectionVars true
variable
  {R : Type*} [RealScalar R]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace R X] [MeasurableSpace X] [BorelSpace X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

set_option linter.unusedVariables false in
open Classical in
theorem SciLean.integral_over_bounding_ball
  (f : X → Y) (A : Set X) (μ : Measure X)
  {center radius}
  (hA : BoundingBall₂ R A center radius) :
  (∫ x in A, f x ∂μ)
  =
  (∫ x in closedBall₂ center radius, if x ∈ A then f x else 0 ∂μ) := sorry_proof

end IntegralOverBoundingBall


----------------------------------------------------------------------------------------------------

open Scalar
open Set in
set_option linter.unusedVariables false in
@[gtrans]
theorem Set.prod.bounding_ball₂
    (A : Set X) (B : Set Y) (cx : X) (cy : Y) (rx ry : R)
    (hA : BoundingBall₂ R A cx rx) (hB : BoundingBall₂ R B cy ry) :
    BoundingBall₂ R (A.prod B) (cx,cy) (sqrt (rx^2 + ry^2)) := sorry_proof


set_option linter.unusedVariables false in
@[gtrans]
theorem SProd.sprod.bounding_ball₂
    (A : Set X) (B : Set Y) (cx : X) (cy : Y) (rx ry : R)
    (hA : BoundingBall₂ R A cx rx) (hB : BoundingBall₂ R B cy ry) :
    BoundingBall₂ R (A ×ˢ B) (cx,cy) (sqrt (rx^2 + ry^2)) := sorry_proof


set_option linter.unusedVariables false in
@[gtrans]
theorem Set.fst.bounding_ball₂
    (A : Set (X×Y)) (b : Y) (center : X×Y) (radius : R)
    (hA : BoundingBall₂ R A center radius) :
    let center' := center.1
    let radius' := sqrt (radius^2 - ‖center.2 - b‖₂²[R])
    BoundingBall₂ R (A.fst b) center' radius' := sorry_proof


set_option linter.unusedVariables false in
@[gtrans]
theorem Set.snd.bounding_ball₂
    (A : Set (X×Y)) (a : X) (center : X×Y) (radius : R)
    (hA : BoundingBall₂ R A center radius) :
    BoundingBall₂ R (A.snd a)
      (let center := center
       center.2)
      (let center := center
       sqrt (radius^2 - ‖center.1 - a‖₂²)) := sorry_proof


set_option linter.unusedVariables false in
@[gtrans]
theorem Set.inter.left_bounding_ball₂
    (A B : Set X) (center : X) (radius : R)
    (hA : BoundingBall₂ R A center radius) :
    BoundingBall₂ R (A ∩ B) center radius := sorry_proof

set_option linter.unusedVariables false in
@[gtrans]
theorem Set.inter.right_bounding_ball₂
    (A B : Set X) (center : X) (radius : R)
    (hB : BoundingBall₂ R B center radius) :
    BoundingBall₂ R (A ∩ B) center radius := sorry_proof

-- TODO: make sure that we can do bounding balls on `R×R` or similar
--       I somehow need to make sure that Preorder structure is compatible with
--       the distance function

@[gtrans]
theorem Set.Icc.bounding_ball₂ (a b : R) :
    BoundingBall₂ R (Icc a b) ((a + b)/2) ((b-a)/2) := sorry_proof

@[gtrans]
theorem Set.Ioo.bounding_ball₂ (a b : R) :
    BoundingBall₂ R (Ioo a b) ((a + b)/2) ((b-a)/2) := sorry_proof

@[gtrans]
theorem Set.Ico.bounding_ball₂ (a b : R) :
    BoundingBall₂ R (Ico a b) ((a + b)/2) ((b-a)/2) := sorry_proof

@[gtrans]
theorem Set.Ioc.bounding_ball₂ (a b : R) :
    BoundingBall₂ R (Ioc a b) ((a + b)/2) ((b-a)/2) := sorry_proof
