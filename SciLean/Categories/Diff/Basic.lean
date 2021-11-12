 import SciLean.Algebra
import SciLean.Categories.Smooth

namespace SciLean

variable {X Y} [Vec X] [Vec Y]

-- Move this to Mathlib
def convenient.is_diff (f : X → Y) : Prop := sorry

class IsDiff (f : X → Y) : Prop := (is_diff : convenient.is_diff f)

instance (f : X → Y) [IsDiff f] : FetchProof IsDiff f := by constructor; assumption

def DiffMap (X Y : Type) [Vec X] [Vec Y] := { f : X → Y // IsDiff f }

instance (f : X → Y) [IsSmooth f] : IsDiff f := sorry
