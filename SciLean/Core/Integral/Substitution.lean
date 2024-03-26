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
  {X₁ : I → Type} [∀ i, SemiHilbert R (X₁ i)] [∀ i, MeasureSpace (X₁ i)]
  {X₂ : I → Type} [∀ i, SemiHilbert R (X₂ i)]

open FiniteDimensional

open BigOperators in
theorem intetgral_parametric_inverse [Fintype I] (φ ψ : X → W) (f : X → Y) (hdim : d = finrank R X - finrank R W)
  {p : (i : I) → X₁ i → X₂ i → X} {ζ : (i : I) → X₁ i → X₂ i} {dom : (i : I) → Set (X₁ i)}
  (inv : ParametricInverseAt (fun x => φ x - ψ x) 0 p ζ dom) :
  ∫' x in {x' | φ x' = ψ x'}, f x ∂(surfaceMeasure d)
  =
  ∑ i, ∫' x₁ in dom i, jacobian R (fun x => p i x (ζ i x)) x₁ • f (p i x₁ (ζ i x₁)) := sorry_proof
