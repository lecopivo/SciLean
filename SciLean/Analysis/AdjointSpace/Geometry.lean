import SciLean.Analysis.AdjointSpace.Basic
import SciLean.Analysis.Normed.Norm2
import SciLean.Analysis.Scalar

namespace SciLean

variable
  {R} [RealScalar R]
  {X} [NormedAddCommGroup X] [AdjointSpace R X]



/-- Ball using standard Euclidean metric. Empty for negative `r`.

Similar to `Metric.ball` but uses norm originating from inner produce. Note that `ℝ×ℝ` uses
max norm therefore for `x : ℝ×ℝ` the `Metric.ball x r` is is square rather then a ball.   -/
def ball₂ (x : X) (r : R) := {y | ‖y - x‖₂²[R] < r^2}


/-- Closed ball using standard Euclidean metric. Empty for negative `r`.

Similar to `Metric.closedBall` but uses norm originating from inner produce. Note that `ℝ×ℝ` uses
max norm therefore for `x : ℝ×ℝ` the `Metric.ball x r` is is square rather then a ball.   -/
def closedBall₂ (x : X) (r : R) := {y | ‖y - x‖₂²[R] ≤ r^2}


/-- Sphere using standard Euclidean metric. Empty for negative `r`.

Similar to `Metric.sphere` but uses norm originating from inner produce. Note that `ℝ×ℝ` uses
max norm therefore for `x : ℝ×ℝ` the `Metric.sphere x r` is is square rather then a sphere.   -/
def sphere₂ (x : X) (r : R) := {y | ‖y - x‖₂²[R] = r^2}


@[simp,simp_core]
theorem frontier_ball₂ (x : X) (r : R) : frontier (ball₂ x r) = sphere₂ x r := sorry_proof

@[simp,simp_core]
theorem frontier_closedBall₂ (x : X) (r : R) : frontier (closedBall₂ x r) = sphere₂ x r := sorry_proof

@[simp,simp_core]
theorem interior_ball₂ (x : X) (r : R) : interior (ball₂ x r) = ball₂ x r := sorry_proof

@[simp,simp_core]
theorem interior_closedBall₂ (x : X) (r : R) : interior (closedBall₂ x r) = ball₂ x r := sorry_proof

@[simp,simp_core]
theorem closure_ball₂ (x : X) (r : R) : closure (ball₂ x r) = closedBall₂ x r := sorry_proof

@[simp,simp_core]
theorem closure_closedBall₂ (x : X) (r : R) : closure (closedBall₂ x r) = closedBall₂ x r := sorry_proof
