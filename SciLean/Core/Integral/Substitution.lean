import SciLean.Core.Integral.CIntegral
import SciLean.Core.Integral.ParametricInverse
import SciLean.Core.Integral.Surface
import SciLean.Core.Integral.Jacobian


open MeasureTheory

namespace SciLean

variable
  {R} [RealScalar R]
  {W} [SemiHilbert R W]
  {V} [SemiHilbert R V]
  {X} [SemiHilbert R X] [MeasureSpace X]
  {Y} [SemiHilbert R Y] [Module ℝ Y]
  {Z} [SemiHilbert R Z] [Module ℝ Z]
  {X₁ : I → Type}
  {X₂ : I → Type}

open FiniteDimensional

-- open BigOperators in
-- @[ftrans_simp]
-- theorem integral_parametric_inverse (φ ψ : X → W) (f : X → Y) (hdim : d = finrank R X - finrank R W)  {p : (i : I) → X₁ i → X₂ i → X} {ζ : (i : I) → X₁ i → X₂ i} {dom : (i : I) → Set (X₁ i)}
--   (inv : ParametricInverseAt (fun x => φ x - ψ x) 0 p ζ dom)
--   [Fintype I] [∀ i, SemiHilbert R (X₁ i)] [∀ i, MeasureSpace (X₁ i)] :
--   ∫' x in {x' | φ x' = ψ x'}, f x ∂(surfaceMeasure d)
--   =
--   Finset.sum Finset.univ (fun i => ∫' x₁ in dom i, jacobian R (fun x => p i x (ζ i x)) x₁ • f (p i x₁ (ζ i x₁))) := sorry_proof
