import SciLean.Core
import SciLean.Functions.Limit

namespace SciLean


def gradientDescent [Vec X] (gradf : X → X) (x₀ : X) (s : ℝ) (steps : Nat) : X := Id.run do
  let mut x := x₀
  for i in [0:steps] do
    x := x - s • gradf x
  x

theorem argminFun.approx.gradientDescent {X} [Hilbert X] {f : X → ℝ} (x₀ : X) (s : ℝ)
  : argmin x, f x 
    =
    limit λ n => gradientDescent (∇ f) x₀ s n
  := sorry_proof
