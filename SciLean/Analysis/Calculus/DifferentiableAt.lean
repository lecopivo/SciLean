import SciLean.Analysis.Calculus.FDeriv

namespace SciLean

/--
  Enhanced differentiability at a point, allowing for functions like 1/x that are
  differentiable everywhere except at specific points.
  
  This implementation focuses on:
  - Defining differentiability at a point with domain restrictions
  - Providing rules for common functions like 1/x
-/

variable {K : Type} [RCLike K]
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace K X] [NormedAddCommGroup Y] [NormedSpace K Y]

/-- A function is differentiable at a point with a domain restriction -/
structure DifferentiableAtWithDomain (f : X → Y) (x : X) where
  domain : Set X
  contains_x : x ∈ domain
  differentiable : DifferentiableAt K (fun x' => f x') x

/-- Inverse function is differentiable at all points except 0 -/
theorem inverse_differentiable_at (x : K) (h : x ≠ 0) : 
  DifferentiableAtWithDomain (fun x => x⁻¹) x := {
  domain := {x | x ≠ 0}
  contains_x := h
  differentiable := sorry_proof
}

/-- Division is differentiable when the denominator is non-zero -/
theorem division_differentiable_at (x y : K) (h : y ≠ 0) :
  DifferentiableAtWithDomain (fun p => p.1 / p.2) (x, y) := {
  domain := {p | p.2 ≠ 0}
  contains_x := h
  differentiable := sorry_proof
}

/-- Logarithm is differentiable for positive inputs -/
theorem log_differentiable_at (x : K) (h : x > 0) :
  DifferentiableAtWithDomain (fun x => log x) x := {
  domain := {x | x > 0}
  contains_x := h
  differentiable := sorry_proof
}

/-- Square root is differentiable for positive inputs -/
theorem sqrt_differentiable_at (x : K) (h : x > 0) :
  DifferentiableAtWithDomain (fun x => sqrt x) x := {
  domain := {x | x > 0}
  contains_x := h
  differentiable := sorry_proof
}

end SciLean
