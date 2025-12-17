/-
Float utilities for SciLean

Lean 4 stdlib doesn't provide Float.inf/negInf, so we define them here
using IEEE 754 division by zero semantics.
-/

/-- IEEE 754 positive infinity -/
def Float.inf : Float := 1.0 / 0.0

/-- IEEE 754 negative infinity -/
def Float.negInf : Float := -1.0 / 0.0
