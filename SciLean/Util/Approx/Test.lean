import SciLean.Util.Approx.Basic
import SciLean
import SciLean.Util.RewriteBy
import SciLean.Util.Limit

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
    := sorry


approx sqrt_approx := isomorph `RealToFloat Real.sqrt
by
  rw[sqrtBabylonianLimit 1]
  apply Approx.limit; intro n


#eval! sqrt_approx (0,()) 2
#eval! sqrt_approx (1,()) 2
#eval! sqrt_approx (2,()) 2
#eval! sqrt_approx (3,()) 2
#eval! sqrt_approx (4,()) 2
