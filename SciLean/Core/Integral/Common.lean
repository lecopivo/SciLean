import SciLean.Core.Integral.HasDerivUnderIntegral
import SciLean.Core.Integral.RnDeriv
import SciLean.Core.Integral.Substitution
import SciLean.Core.Integral.PlaneDecomposition

open MeasureTheory

namespace SciLean

macro "integral_deriv" : conv =>
  `(conv| fun_trans (config:={zeta:=false}) (disch:=first | assumption | (gtrans (disch:=(first | assumption | fun_prop (disch:=assumption))))) only
      [↓ refinedRewritePre, ↑ refinedRewritePost, ftrans_simp, Tactic.lift_lets_simproc,
       scalarGradient, scalarCDeriv])


attribute [ftrans_simp] ite_smul

attribute [ftrans_simp] MeasureTheory.Measure.restrict_empty MeasureTheory.Measure.zero_toOuterMeasure MeasureTheory.OuterMeasure.coe_zero MeasureTheory.Measure.restrict_univ

attribute [ftrans_simp] ENNReal.one_toReal ENNReal.zero_toReal


----------------------------------------------------------------------------------------------------
-- Measure simp theorems ---------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- same as `MeasureTheory.Measure.restrict_restrict` but for now we skip checking measurability of the set
@[ftrans_simp]
theorem Measure.restrict_restrict {X} [MeasurableSpace X] (μ : Measure X) (A B : Set X) :
    (μ.restrict A).restrict B = μ.restrict (A ∩ B) := by sorry_proof

@[ftrans_simp]
theorem Measure.prod_restrict {X Y} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (A : Set X) (B : Set Y) :
    (Measure.prod (μ.restrict A) (ν.restrict B)) = (μ.prod ν).restrict (A ×ˢ B) := by sorry_proof

@[ftrans_simp]
theorem Measure.prod_volume {X Y} [MeasureSpace X] [MeasureSpace Y]  :
    (Measure.prod (volume : Measure X) (volume : Measure Y)) = volume := by sorry_proof



----------------------------------------------------------------------------------------------------
-- Substitution theorems ---------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section SubstitutionTheorems

variable
  {R} [RealScalar R]
  {U V W : Type}
  {S : Type} [Vec R S]
  {X : Type} [SemiHilbert R X] [MeasureSpace X]
  {Y : Type} [MeasurableSpace Y]
  [AddCommGroup U] [Module R U] [Module ℝ U] [TopologicalSpace U]
  -- [Vec R U] [Module ℝ U]
  [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]


open FiniteDimensional


-- WARNING: changing assumption
--          [AddCommGroup U] [Module R U] [Module ℝ U] [TopologicalSpace U]
--          to
--          [Vec R U] [Module ℝ U]
--          makes this theorem to fail unification
open BigOperators in
@[ftrans_simp]
theorem surfaceIntegral_parametrization (f : X → U) (d) (φ ψ : X → R)
    {I} {X₁ X₂ : I → Type}
    (p : (i : I) → X₁ i → X₂ i → X) (g : (i : I) → X₁ i → X₂ i) (dom : (i : I) → Set (X₁ i))
    (hinv : ParametricInverseAt (fun x => φ x - ψ x) 0 p g dom)
    [Fintype I] [∀ i, SemiHilbert R (X₁ i)] [∀ i, MeasureSpace (X₁ i)] :
    ∫' x in {x | φ x = ψ x}, f x ∂((surfaceMeasure d))
    =
    let sub := fun i x => p i x (g i x)
    let J := fun i x => jacobian R (sub i) x
    ∑ i : I, ∫' x in dom i, J i x • f (sub i x) := sorry_proof


open BigOperators in
@[ftrans_simp]
theorem surfaceIntegral_inter_parametrization (f : X → U) (d) (φ ψ : X → R) (A : Set X)
    {I} {X₁ X₂ : I → Type}
    (p : (i : I) → X₁ i → X₂ i → X) (g : (i : I) → X₁ i → X₂ i) (dom : (i : I) → Set (X₁ i))
    (hinv : ParametricInverseAt (fun x => φ x - ψ x) 0 p g dom)
    [Fintype I] [∀ i, SemiHilbert R (X₁ i)] [∀ i, MeasureSpace (X₁ i)] :
    ∫' x in {x | φ x = ψ x} ∩ A, f x ∂((surfaceMeasure d))
    =
    ∑ i : I,
      let sub := fun x => p i x (g i x)
      let J := fun x => jacobian R sub x
      ∫' x in sub ⁻¹' A ∩ dom i, J x • f (sub x) := sorry_proof


end SubstitutionTheorems



----------------------------------------------------------------------------------------------------
-- Unit - integral and measure theorems ------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[ftrans_simp]
theorem cintegral_over_unit {X} [AddCommGroup X] [Module ℝ X] (f : Unit → X) (μ : Measure Unit) :
    ∫' (x : Unit), f x ∂μ
    =
    (μ ⊤).toReal • f () := sorry_proof

@[simp,ftrans_simp]
theorem volume_univ_unit : volume (⊤ : Set Unit) = 1 := sorry_proof


@[simp, ftrans_simp]
theorem _root_.FiniteDimensional.finrank_unit {R} [Ring R] :
    FiniteDimensional.finrank R Unit = 0 := sorry_proof





----------------------------------------------------------------------------------------------------
-- if .. then .. else .. - pulling if out of important functions -----------------------------------
----------------------------------------------------------------------------------------------------


@[simp,ftrans_simp]
theorem ite_pull_measure_restrict {X} [MeasurableSpace X] (c : Prop) [Decidable c] (μ : Measure X) (A B : Set X) :
    μ.restrict (if c then A else B)
    =
    if c then μ.restrict A else μ.restrict B:= sorry_proof



@[simp,ftrans_simp]
theorem ite_pull_measureOf {X} [MeasurableSpace X] (c : Prop) [Decidable c] (μ ν : Measure X) (A : Set X) :
    (if c then μ else ν) A
    =
    (if c then μ A else ν A) := by sorry_proof

@[simp,ftrans_simp]
theorem ite_pull_ennreal_toReal (c : Prop) [Decidable c] (x y : ENNReal)  :
    (if c then x else y).toReal
    =
    (if c then x.toReal else y.toReal) := by sorry_proof
