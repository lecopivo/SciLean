import SciLean.Basic
import SciLean.Mechanics


open Function
namespace SciLean

def H (n : Nat) (m k : ℝ) (x p : ℝ^n) := (2/m) * ⟪p,p⟫ + 2*k * ⟪x, x⟫
