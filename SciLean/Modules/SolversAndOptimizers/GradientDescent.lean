import SciLean.Core
import SciLean.Core.Functions.ArgMinMax
import SciLean.Util.Limit

namespace SciLean

open Notation

variable {R} [RealScalar R]

set_default_scalar R

def gradientDescent [Vec R X] (gradf : X → X) (x₀ : X) (s : R) (steps : Nat) : X := Id.run do
  let mut x := x₀
  for i in [0:steps] do
    x := x - s • gradf x
  x

theorem argminFun.approx.gradientDescent {X} [SemiHilbert R X] {f : X → R} (x₀ : X) (s : R)
  : (argmin x, f x)
    =
    limit n → ∞, gradientDescent (∇ f) x₀ s n
  := sorry_proof
