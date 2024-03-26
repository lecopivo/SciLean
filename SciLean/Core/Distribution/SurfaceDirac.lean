import SciLean.Core.Distribution.Basic
import SciLean.Core.Distribution.ParametricDistribDeriv
import SciLean.Core.Integral.Surface
import SciLean.Core.Integral.MovingDomain
import SciLean.Core.Integral.Jacobian


open MeasureTheory FiniteDimensional

namespace SciLean

variable
  {R} [RealScalar R]
  {W} [Vec R W]
  {X} [SemiHilbert R X] [MeasureSpace X]

set_default_scalar R


open Classical
noncomputable
def surfaceDirac (A : Set X) (f : X → R) (d : ℕ) : 𝒟' X :=
  ⟨fun φ ⊸ ∫' x in A, φ x * f x ∂(surfaceMeasure d)⟩


@[action_push]
theorem surfaceDirac_action (A : Set X) (f : X → R) (d : ℕ) (φ : 𝒟 X) :
    (surfaceDirac A f d).action φ = ∫' x in A, φ x * f x ∂(surfaceMeasure d) := sorry_proof

@[action_push]
theorem surfaceDirac_extAction (A : Set X) (f : X → R) (d : ℕ) (φ : X → R) :
    (surfaceDirac A f d).extAction φ = ∫' x in A, φ x * f x ∂(surfaceMeasure d) := sorry_proof


@[simp, ftrans_simp]
theorem surfaceDirac_dirac (f : X → R) (x : X) : surfaceDirac {x} f 0 = f x • dirac x := sorry_proof


open Classical Function in
@[fun_trans]
theorem ite_parDistribDeriv (A : W → Set X) (f g : W → X → R) :
    parDistribDeriv (fun w => Function.toDistribution (fun x => if x ∈ A w then f w x else g w x))
    =
    fun w dw =>
      surfaceDirac (frontier (A w)) (fun x => (frontierSpeed R A w dw x) * (f w x - g w x)) (finrank R X - 1)
      +
      ifD (A w) then
        (parDistribDeriv (fun w => (f w ·).toDistribution) w dw)
      else
        (parDistribDeriv (fun w => (g w ·).toDistribution) w dw) := sorry_proof


open Function in
@[fun_trans]
theorem ite_parDistribDeriv' (φ ψ : W → X → R) (f g : W → X → R) :
    parDistribDeriv (fun w => Function.toDistribution (fun x => if φ w x ≤ ψ w x then f w x else g w x))
    =
    fun w dw =>
      let frontierSpeed := fun x => - (∂ (w':=w;dw), (φ w' x - ψ w' x)) / ‖∇ (x':=x), (φ w x' - ψ w x')‖₂
      (surfaceDirac {x | φ w x = ψ w x} frontierSpeed (finrank R X - 1))
      +
      ifD {x | φ w x ≤ ψ w x} then
        (parDistribDeriv (fun w => (f w ·).toDistribution) w dw)
      else
        (parDistribDeriv (fun w => (g w ·).toDistribution) w dw) := sorry_proof


open Function in
@[fun_trans]
theorem toDistribution.arg_f.parDistribDeriv_rule (f : W → X → R) (hf : ∀ x, CDifferentiable R (f · x)) :
    parDistribDeriv (fun w => Function.toDistribution (fun x => f w x))
    =
    fun w dw =>
      (Function.toDistribution (fun x => cderiv R (f · x) w dw)) := by

  unfold parDistribDeriv
  funext x dx; ext φ
  sorry_proof


----------------------------------------------------------------------------------------------------
-- Substitution ------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


variable
  {I} [Fintype I]
  {X₁ : I → Type} [∀ i, SemiHilbert R (X₁ i)] [∀ i, MeasureSpace (X₁ i)]
  {X₂ : I → Type} [∀ i, Vec R (X₂ i)]

-- open BigOperators in
-- theorem intetgral_parametric_inverse [Fintype I] (φ ψ : X → W) (f : X → Y) (hdim : d = finrank R X - finrank R W)
--   {p : (i : I) → X₁ i → X₂ i → X} {ζ : (i : I) → X₁ i → X₂ i} {dom : (i : I) → Set (X₁ i)}
--   (inv : ParametricInverseAt (fun x => φ x - ψ x) 0 p ζ dom) :
--   ∫' x in {x' | φ x' = ψ x'}, f x ∂(surfaceMeasure d)
--   =
--   ∑ i, ∫' x₁ in dom i, jacobian R (fun x => p i x (ζ i x)) x₁ • f (p i x₁ (ζ i x₁)) := sorry_proof


open BigOperators in
theorem surfaceDirac_substitution [Fintype I] (φ ψ : X → R) (f : X → R) (d : ℕ)
    {p : (i : I) → X₁ i → X₂ i → X} {ζ : (i : I) → X₁ i → X₂ i} {dom : (i : I) → Set (X₁ i)}
    (inv : ParametricInverseAt (fun x => φ x - ψ x) 0 p ζ dom) (hdim : ∀ i, d = finrank (X₁ i)) :
    surfaceDirac {x | φ x = ψ x} f d
    =
    ∑ i, Distribution.prod'
           (fun x₁ x₂ => p i x₁ x₂)
           (((fun x₁ => jacobian R (fun x => p i x (ζ i x)) x₁ • f (p i x₁ (ζ i x₁)) ).toDistribution : 𝒟' (X₁ i)).restrict (dom i))
           (fun x₁ => (dirac (ζ i x₁) : 𝒟' (X₂ i))) := sorry


#exit

set_option trace.Meta.Tactic.simp.discharge true in
#check (parDistribDeriv (fun w : R =>
  Function.toDistribution
    fun x : R =>
      if 0 ≤ x - w then
        if 0 ≤ x^2 - w^2 then
          if 0 ≤ x^2 + w^2 then
            x + w
          else
            x - w
        else
          x / w
      else
        x * w))
  rewrite_by
    fun_trans (disch:=sorry) only [scalarGradient, ftrans_simp]
    simp only [ftrans_simp, finrank_self, le_refl, tsub_eq_zero_of_le]




set_option trace.Meta.Tactic.simp.discharge true in
#check (cderiv R (fun w : R =>
  ∫' (x : R) in Set.Icc 0 1,
      if 0 ≤ x - w then
        if 0 ≤ x^2 - w^2 then
          if 0 ≤ x^2 + w^2 then
            x + w
          else
            x - w
        else
          x / w
      else
        x * w))
  rewrite_by
    autodiff
    unfold scalarGradient
    autodiff
    -- fun_trans (disch:=sorry) only [scalarGradient, ftrans_simp]
    simp (config:={zeta:=false}) only [ftrans_simp, finrank_self, le_refl, tsub_eq_zero_of_le]
    simp (config:={zeta:=false}) only [ftrans_simp, action_push]
