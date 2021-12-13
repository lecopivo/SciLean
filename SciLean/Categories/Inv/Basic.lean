import SciLean.Algebra

namespace SciLean

class IsInv {α β} (f : α → β) : Prop where
  is_inv : Function.bijective f

def InvMap (α β) := { f : α → β // IsInv f }


