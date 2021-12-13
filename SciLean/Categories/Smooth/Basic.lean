import SciLean.Mathlib.Convenient.Basic
import SciLean.Categories.Lin

namespace SciLean

variable {X Y} [Vec X] [Vec Y]

open SciLean.Mathlib.Convenient

class IsSmooth {X Y} [Vec X] [Vec Y] (f : X → Y) : Prop := (is_smooth : is_smooth f)

-- instance (f : X → Y) [IsSmooth f] : FetchProof IsSmooth f := by constructor; assumption

def SmoothMap (X Y : Type) [Vec X] [Vec Y] := { f : X → Y // IsSmooth f }

instance (priority := low) (f : X → Y) [IsLin f] : IsSmooth f := sorry
