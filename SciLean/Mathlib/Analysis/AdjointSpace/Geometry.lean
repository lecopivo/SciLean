import SciLean.Mathlib.Analysis.AdjointSpace.Basic
import SciLean.Core.Objects.Scalar

namespace SciLean

variable
  {R} [RealScalar R]
  {X} [NormedAddCommGroup X] [AdjointSpace R X]

local notation "‖" x "‖₂²" => @inner R _ _ x x


/-- Ball using standard Euclidean metric. Empty for negative `r`.

Similar to `Metric.ball` but uses norm originating from inner produce. Note that `ℝ×ℝ` uses
max norm therefore for `x : ℝ×ℝ` the `Metric.ball x r` is is square rather then a ball.   -/
def ball₂ (x : X) (r : R) := {y | ‖y - x‖₂² ≤ r}


/-- Closed ball using standard Euclidean metric. Empty for negative `r`.

Similar to `Metric.closedBall` but uses norm originating from inner produce. Note that `ℝ×ℝ` uses
max norm therefore for `x : ℝ×ℝ` the `Metric.ball x r` is is square rather then a ball.   -/
def closedBall₂ (x : X) (r : R) := {y | ‖y - x‖₂² ≤ r}


/-- Sphere using standard Euclidean metric. Empty for negative `r`.

Similar to `Metric.sphere` but uses norm originating from inner produce. Note that `ℝ×ℝ` uses
max norm therefore for `x : ℝ×ℝ` the `Metric.sphere x r` is is square rather then a sphere.   -/
def sphere₂ (x : X) (r : R) := {y | ‖y - x‖₂² = r}


@[simp,ftrans_simp]
theorem frontier_ball₂ (x : X) (r : R) : frontier (ball₂ x r) = sphere₂ x r := sorry_proof

@[simp,ftrans_simp]
theorem frontier_closedBall₂ (x : X) (r : R) : frontier (closedBall₂ x r) = sphere₂ x r := sorry_proof

@[simp,ftrans_simp]
theorem interior_ball₂ (x : X) (r : R) : interior (ball₂ x r) = ball₂ x r := sorry_proof

@[simp,ftrans_simp]
theorem interior_closedBall₂ (x : X) (r : R) : interior (closedBall₂ x r) = ball₂ x r := sorry_proof

@[simp,ftrans_simp]
theorem closure_ball₂ (x : X) (r : R) : closure (ball₂ x r) = closedBall₂ x r := sorry_proof

@[simp,ftrans_simp]
theorem closure_closedBall₂ (x : X) (r : R) : closure (closedBall₂ x r) = closedBall₂ x r := sorry_proof
