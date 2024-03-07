import SciLean.Core.CoreFunctions

namespace SciLean


--------------------------------------------------------------------------------
-- Real.sqrt - √
--------------------------------------------------------------------------------

function_properties SciLean.Real.sqrt [UnsafeAD] (x : ℝ)
argument x
  IsSmooth := sorry_proof,
  abbrev ∂ := λ dx => dx/(2 * x.sqrt) by sorry_proof,
  abbrev 𝒯 := λ dx => let xNorm := ‖x‖; (xNorm, ⟪dx, x⟫/xNorm) by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ dx' => (dx'/‖x‖) • x by sorry_proof,
  abbrev ℛ := let xNorm := ‖x‖; (xNorm, λ dx' => (dx'/‖x‖) • x) by sorry_proof


--------------------------------------------------------------------------------
-- Real.pow - x^y
--------------------------------------------------------------------------------

function_properties SciLean.Real.pow [UnsafeAD] (x y : ℝ)
argument (x,y)
  IsSmooth := sorry_proof,
  abbrev ∂ := λ dx dy => (dy * x.log + dx*y/x)*(x.pow y) by sorry_proof,
  abbrev 𝒯 := λ dx dy => let xy := x.pow y; (xy, (dy * x.log + dx*y/x)*xy) by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ dxy' => let xy := x.pow y; (dxy'*x.log*xy, dxy'*y/x*xy) by sorry_proof,
  abbrev ℛ := let xy := x.pow y; (xy, λ dxy' => (dxy'*x.log*xy, dxy'*y/x*xy)) by sorry_proof
argument x
  IsSmooth := sorry_proof,
  abbrev ∂ := λ dx => dx*y * x^(y-1) by sorry_proof,
  abbrev 𝒯 := λ dx => (x^y, dx*y*x^(y-1)) by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ dx' => dx'*y*x^(y-1) by sorry_proof,
  abbrev ℛ := (x^y,  λ dx' => dx'*y*x^(y-1)) by sorry_proof
argument y
  IsSmooth := sorry_proof,
  abbrev ∂ := λ dy => dy * x.log *(x^y) by sorry_proof,
  abbrev 𝒯 := λ dy => let xy := x.pow y; (xy, dy * x.log * xy) by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ dy' => dy'*x.log*x^y by sorry_proof,
  abbrev ℛ := let xy := x.pow y; (xy, λ dy' => dy'*x.log*xy) by sorry_proof


--------------------------------------------------------------------------------
-- Real.natPow - x^n
--------------------------------------------------------------------------------

function_properties SciLean.Real.natPow (x : ℝ) (n : Nat)
argument x
  IsSmooth := sorry_proof,
  abbrev ∂ := λ dx => (dx * n * x.natPow (n-1)) by sorry_proof,
  abbrev 𝒯 := λ dx => (x.natPow n, dx * n * x.natPow (n-1)) by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ dx' => (dx' * n * x.natPow (n-1)) by sorry_proof,
  abbrev ℛ := (x.natPow n, λ dx' => dx' * n * x.natPow (n-1)) by sorry_proof


--------------------------------------------------------------------------------
-- Real.sin
--------------------------------------------------------------------------------

function_properties SciLean.Real.sin (x : ℝ)
argument x
  IsSmooth := sorry,
  abbrev ∂ := λ dx => dx * x.cos by sorry_proof,
  abbrev 𝒯 := λ dx => (x.sin, dx * x.cos) by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ dx' => dx' * x.cos by sorry_proof,
  abbrev ℛ := (x.sin, λ dx' => dx' * x.cos) by sorry_proof


--------------------------------------------------------------------------------
-- Real.cos
--------------------------------------------------------------------------------

function_properties SciLean.Real.cos (x : ℝ)
argument x
  IsSmooth := sorry,
  abbrev ∂ := λ dx => - dx * x.sin by sorry_proof,
  abbrev 𝒯 := λ dx => (x.cos, - dx * x.sin) by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ dx' => - dx' * x.sin by sorry_proof,
  abbrev ℛ := (x.cos, λ dx' => - dx' * x.sin) by sorry_proof


--------------------------------------------------------------------------------
-- Real.tan
--------------------------------------------------------------------------------

function_properties SciLean.Real.tan [UnsafeAD] (x : ℝ)
argument x
  IsSmooth := sorry,
  abbrev ∂ := λ dx => dx * (1 + x.tan^2) by sorry_proof,
  abbrev 𝒯 := λ dx => let tanx := x.tan; (tanx, dx * (1 + tanx^2)) by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ dx' => dx' * (1 + x.tan^2) by sorry_proof,
  abbrev ℛ := let tanx := x.tan; (tanx, λ dx' => dx' * (1 + tanx^2)) by sorry_proof


--------------------------------------------------------------------------------
-- Real.atan
--------------------------------------------------------------------------------

function_properties SciLean.Real.atan (x : ℝ)
argument x
  IsSmooth := sorry,
  abbrev ∂ := λ dx => dx * (1 + x^2) by sorry_proof,
  abbrev 𝒯 := λ dx => (x.atan, dx * (1 + x^2)) by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ dx' => dx' * (1 + x^2) by sorry_proof,
  abbrev ℛ := (x.atan, λ dx' => dx' * (1 + x^2)) by sorry_proof


--------------------------------------------------------------------------------
-- Real.atan2
--------------------------------------------------------------------------------

function_properties SciLean.Real.atan2 [UnsafeAD] (y x : ℝ)
argument (y,x)
  IsSmooth := sorry,
  abbrev ∂ := λ dy dx => (x * dy - dx * y) / (x^2 + y^2) by sorry_proof,
  abbrev 𝒯 := λ dy dx => (Real.atan2 y x, (x * dy - dx * y) / (x^2 + y^2)) by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ dyx' => let inorm2 := (x^2 + y^2)⁻¹; (dyx'*x*inorm2, -dyx'*y*inorm2) by sorry_proof,
  abbrev ℛ := (Real.atan2 y x, λ dyx' => let inorm2 := (x^2 + y^2)⁻¹; (dyx'*x*inorm2, -dyx'*y*inorm2)) by sorry_proof


--------------------------------------------------------------------------------
-- Real.exp
--------------------------------------------------------------------------------

function_properties SciLean.Real.exp (x : ℝ)
argument x
  IsSmooth := sorry,
  abbrev ∂ := λ dx => dx * x.exp by sorry_proof,
  abbrev 𝒯 := λ dx => let expx := x.exp; (expx, dx * expx) by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ dx' => dx' * x.exp by sorry_proof,
  abbrev ℛ := let expx := x.exp; (expx, λ dx' => dx' * expx) by sorry_proof
