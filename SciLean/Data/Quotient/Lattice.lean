import Mathlib

namespace SciLean

-- also called Meet, ⊓ \glb
class GreatestLowerBound (α : Type u) where
  glb : α → α → α

-- also called Join, ⊔ \lub
class LowestUpperBound (α : Type u) where
  lub : α → α → α

class GreatestElement (α : Type u) where
  top : α

class LowestElement (α : Type u) where
  bottom : α

infix:35 " ⊓ " => GreatestLowerBound.glb
infix:30 " ⊔ " => LowestUpperBound.lub
notation " ⊤ " => GreatestElement.top
notation " ⊥ " => LowestElement.bottom

-- TODO: Add decidability
class BoundedLattice (α : Type u) extends PartialOrder α, GreatestLowerBound α, LowestUpperBound α, GreatestElement α, LowestElement α where
  -- meet is the greatest lower bound
  -- join is the smallest upper bound
  le_bottom : ∀ x : α, ⊥ ≤ x
  le_top    : ∀ x : α, x ≤ ⊤
