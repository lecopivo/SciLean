import SciLean.Core.FloatAsReal
import SciLean.Util.RewriteBy

open SciLean

def sqrtBabylonian (n : Nat) (x₀ : Float) (y : Float) : Float := 
match n with
| 0   => x₀ 
| n'+1 => sqrtBabylonian n' ((x₀ + y/x₀)/2) y



#check (isomorph `RealToFloat Real.sqrt) rewrite_by ftrans

