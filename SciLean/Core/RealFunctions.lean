import SciLean.Core.CoreFunctions

namespace SciLean


function_properties SciLean.Real.sqrt [UnsafeAD] (x : ℝ) 
argument x
  IsSmooth := sorry,
  abbrev ∂ := λ dx => dx/(2 * x.sqrt) by sorry,
  abbrev 𝒯 := λ dx => let xNorm := ‖x‖; (xNorm, ⟪dx, x⟫/xNorm) by sorry,
  HasAdjDiff := sorry,
  abbrev ∂† := λ dx' => (dx'/‖x‖) • x by sorry,
  abbrev ℛ := let xNorm := ‖x‖; (xNorm, λ dx' => (dx'/‖x‖) • x) by sorry


function_properties SciLean.Real.pow [UnsafeAD] (x y : ℝ) 
argument (x,y)
  IsSmooth := sorry,
  abbrev ∂ := λ dx dy => (dy * x.log + dx*y/x)*(x.pow y) by sorry,
  abbrev 𝒯 := λ dx dy => let xy := x.pow y; (xy, (dy * x.log + dx*y/x)*xy) by sorry,
  HasAdjDiff := sorry,
  abbrev ∂† := λ dxy' => let xy := x.pow y; (dxy'*x.log*xy, dxy'*y/x*xy) by sorry,
  abbrev ℛ := let xy := x.pow y; (xy, λ dxy' => (dxy'*x.log*xy, dxy'*y/x*xy)) by sorry

