import SciLean.Algebra
-- import SciLean.Categories.Basic

namespace SciLean

set_option synthInstance.maxHeartbeats 5000

class IsLin {U V} [Vec U] [Vec V] (f : U → V) : Prop :=
  ( add : ∀ x y, f (x + y) = f x + f y )
  ( mul : ∀ (s : ℝ) x, f (s*x) = s * (f x) )

set_option synthInstance.maxHeartbeats 500

def LinMap (X Y : Type) [Vec X] [Vec Y] := { f : X → Y // IsLin f }


