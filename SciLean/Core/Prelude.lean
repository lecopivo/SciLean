import SciLean.Algebra

namespace SciLean

def hold {α} (a : α) := a

@[inline] 
def kron {ι} [DecidableEq ι] (i j : ι) : ℝ := if (i=j) then 1 else 0

class Fact (P : Prop) where
  proof : P

instance : Fact (x=x) := ⟨by rfl⟩
