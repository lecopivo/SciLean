import SciLean.Core.Distribution.Basic
import SciLean.Core.Distribution.ParametricDistribDeriv
import SciLean.Core.Integral.Surface
import SciLean.Core.Integral.MovingDomain

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
  ⟨fun φ => ∫' x in A, φ x * f x ∂(surfaceMeasure d)⟩


@[simp, ftrans_simp]
theorem surfaceDirac_pure (f : X → R) (x : X) : surfaceDirac {x} f 0 = f x • pure x := sorry_proof


open Classical Function in
@[fun_trans]
theorem ite_parDistribDeriv (A : W → Set X) (f g : W → X → R) :
    parDistribDeriv deg (fun w => Function.toDistribution (fun x => if x ∈ A w then f w x else g w x))
    =
    fun w dw =>
      surfaceDirac (frontier (A w)) (fun x => (frontierSpeed R A w dw x) * (f w x - g w x)) (finrank R X - 1)
      +
      ifD (A w) then
        (parDistribDeriv deg (fun w => (f w ·).toDistribution) w dw)
      else
        (parDistribDeriv deg (fun w => (g w ·).toDistribution) w dw) := sorry_proof


open Function in
@[fun_trans]
theorem ite_parDistribDeriv' (φ ψ : W → X → R) (f g : W → X → R) :
    parDistribDeriv deg (fun w => Function.toDistribution (fun x => if φ w x ≤ ψ w x then f w x else g w x))
    =
    fun w dw =>
      let frontierSpeed := fun x => - (∂ (w':=w;dw), (ψ w' x - φ w' x)) / ‖∇ (x':=x), (ψ w x' - φ w x')‖₂
      (surfaceDirac {x | φ w x = ψ w x} frontierSpeed (finrank R X - 1)).restrictDeg deg
      +
      ifD {x | φ w x ≤ ψ w x} then
        (parDistribDeriv deg (fun w => (f w ·).toDistribution) w dw)
      else
        (parDistribDeriv deg (fun w => (g w ·).toDistribution) w dw) := sorry_proof


open Function in
@[fun_trans]
theorem toDistribution.arg_f.parDistribDeriv_rule (f : W → X → R) (hf : ∀ x, CDifferentiable R (f · x)) :
    parDistribDeriv deg (fun w => Function.toDistribution (fun x => f w x))
    =
    fun w dw =>
      (Function.toDistribution (fun x => cderiv R (f · x) w dw)).restrictDeg deg := by

  unfold parDistribDeriv
  funext x dx; ext φ
  if h : ContCDiff R deg φ then
    simp[h]
    fun_trans
  else
    simp[h]



variable (deg) [MeasureSpace R]




set_option trace.Meta.Tactic.simp.discharge true in
#check (parDistribDeriv deg (fun w : R =>
  Function.toDistribution
    fun x : R =>
      if 0 ≤ x - w then
        if 0 ≤ x^2 - w^2 then
          x + w
        else
          x / w
      else
        x * w))
  rewrite_by
    fun_trans (disch:=sorry) only [scalarGradient, ftrans_simp]
    simp only [ftrans_simp, finrank_self, le_refl, tsub_eq_zero_of_le]
