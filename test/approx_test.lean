import SciLean

open SciLean
open Notation


def sqrtBabylonian (n : Nat) (x₀ : Float) (y : Float) : Float :=
match n with
| 0   => x₀
| n'+1 => sqrtBabylonian n' ((x₀ + y/x₀)/2) y


theorem sqrtBabylonianLimit (x₀ : Float) :
    isomorph `RealToFloat Real.sqrt
    =
    limit n → ∞, sqrtBabylonian n x₀
    := sorry_proof


approx sqrt_approx := isomorph `RealToFloat Real.sqrt
by
  rw[sqrtBabylonianLimit 1]
  apply Approx.limit; intro n


/-- info: 1.000000 -/
#guard_msgs in
#eval! sqrt_approx (0,()) 2

/-- info: 1.500000 -/
#guard_msgs in
#eval! sqrt_approx (1,()) 2

/-- info: 1.416667 -/
#guard_msgs in
#eval! sqrt_approx (2,()) 2

/-- info: 1.414216 -/
#guard_msgs in
#eval! sqrt_approx (3,()) 2

/-- info: 1.414214 -/
#guard_msgs in
#eval! sqrt_approx (4,()) 2
