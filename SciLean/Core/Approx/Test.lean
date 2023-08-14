import SciLean.Core.Approx.Basic
import SciLean.Core.FloatAsReal
import SciLean.Util.RewriteBy

open SciLean
open LimitNotation


def sqrtBabylonian (n : Nat) (x₀ : Float) (y : Float) : Float := 
match n with
| 0   => x₀ 
| n'+1 => sqrtBabylonian n' ((x₀ + y/x₀)/2) y

theorem sqrtBabylonianLimit (x₀ : Float) 
  : isomorph `RealToFloat Real.sqrt
    = 
    limit n → ∞, sqrtBabylonian n x₀
    := sorry

approx sqrt_approx := isomorph `RealToFloat Real.sqrt
by
  simp
  rw[sqrtBabylonianLimit 1]
  apply Approx.limit; intro n
  

#eval sqrt_approx (0,()) 2
#eval sqrt_approx (1,()) 2
#eval sqrt_approx (2,()) 2
#eval sqrt_approx (3,()) 2
#eval sqrt_approx (4,()) 2
