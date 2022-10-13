import SciLean.Core
import SciLean.Data.DataArray
import SciLean.Tactic.ConvIf

namespace SciLean

namespace Curve
-- instance : CoeFun (BezierCurve X deg) (λ _ => ℝ → X) := ⟨λ γ => γ.eval⟩

def sampleAdaptive {X} [Hilbert X]
  (γ : ℝ → X) (dγ : AutoImpl (ⅆ γ)) (t₀ t₁ : ℝ) (minPoints maxPoints : ℕ) 
  (_ : (t₀ < t₁) ∧ (2 ≤ minPoints) ∧ (minPoints ≤ maxPoints)) -- assumptions
  : Array X := 
Id.run do
  let mut points : Array X := #[γ t₀]
  let minStep := (t₁ - t₀) / (maxPoints - 1)
  let maxStep := (t₁ - t₀) / (minPoints - 1)
  let mut t := t₀
  for _ in [0 : maxPoints] do

    let change := ∥dγ.val t∥

    if change = 0 then
      t += maxStep 
    else 
      t += min (max (1/change) minStep) maxStep

    if t≥t₁ then
      points := points.push (γ t₁)
      break
    else 
      points := points.push (γ t)

  points



-- = daeSolve (f t γ := 0) (g t γ := ⟪η t, γ⟫) (γ₀)

-- noncomputable
-- def parallelTransport (γ : ℝ → X) (v₀ : X) : ℝ → X := 
--   SolutionOf (λ v μ => (∀ t, ⅆ v t = μ t) ∧ (∀ t, ⟪v t, ⅆ γ t⟫ = ⟪v₀, ⅆ γ 0⟫) ∧ (v 0 = v₀))
     -- where `v` is the solution and `μ` is a Lagrange multiplier 

  -- This is more direct but less readable
  -- daeSolve (λ t x y => y) (λ t x y => ⟪x, ⅆ γ t⟫ - ⟪x₀, ⅆ γ 0⟫) x₀ 
