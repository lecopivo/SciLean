import SciLean.Algebra
import SciLean.Categories.Diff

namespace SciLean

variable {X Y} [Vec X] [Vec Y]

-- Move this to Mathlib
def is_continuous (f : X → Y) : Prop := sorry

class IsCont (f : X → Y) : Prop := (is_cont : is_continuous f)

instance (f : X → Y) [IsCont f] : FetchProof IsCont f := by constructor; assumption

def ContMap (X Y : Type) [Vec X] [Vec Y] := { f : X → Y // IsCont f }

instance (f : X → Y) [IsDiff f] : IsCont f := sorry
