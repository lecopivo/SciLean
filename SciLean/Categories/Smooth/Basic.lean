import SciLean.Algebra
-- import SciLean.Categories.Basic
import SciLean.Categories.Lin

namespace SciLean

variable {X Y} [Vec X] [Vec Y]

-- Move this to Mathlib
def convenient.is_smooth (f : X → Y) : Prop := sorry

class IsSmooth {X Y} [Vec X] [Vec Y] (f : X → Y) : Prop := (is_diff : convenient.is_smooth f)

-- instance (f : X → Y) [IsSmooth f] : FetchProof IsSmooth f := by constructor; assumption

def SmoothMap (X Y : Type) [Vec X] [Vec Y] := { f : X → Y // IsSmooth f }

-- instance (f : X → Y) [IsLin f] : IsSmooth f := sorry
