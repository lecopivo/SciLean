import SciLean.Core.Objects.Vec
import SciLean.Core.Objects.Scalar


namespace SciLean

-- todo: maybe rename to `ParametricPreimageAt` as that might capture the meaning better
def ParametricInverseAt
    {X Y I : Type} {X₁ X₂ : I → Type}
    (f : X → Y) (y : Y)
    (p : ∀ i, X₁ i → X₂ i → X) (g : (i : I) → X₁ i → X₂ i) (dom : (i : I) → Set (X₁ i)) :=
  ∀ (i : I) (x₁ : X₁ i), (x₁∈ dom i) → f (p i x₁ (g i x₁)) = y


variable {R} [RealScalar R]

open Scalar Set

theorem parametric_inverse_bijection [Nonempty X] (f : X → Y) (hf : f.Bijective) (y : Y):
    ParametricInverseAt f y
      (I := Unit) (X₁ := fun _ => Unit)
      (p := fun _ _ x => x)
      (g := fun _ _ => f.invFun y)
      (dom := fun _ => Set.univ) := by
  intro i x _
  simp only
  sorry_proof

theorem circle_polar_inverse (r2 : R) (h : 0 < r2) :
    ParametricInverseAt
      (fun x : R×R => x.1^2 + x.2^2 - r2) 0
      (I := Unit)
      (p := fun _ θ r => r • (cos θ, sin θ))
      (g := fun _ _ => sqrt r2)
      (dom := fun _ => Ioc (-RealScalar.pi) (RealScalar.pi)) := sorry_proof

theorem circle_polar_inverse' (r2 : R) (h : 0 < r2) :
    ParametricInverseAt
      (fun x : R×R => r2 - (x.1^2 + x.2^2)) 0
      (I := Unit)
      (p := fun _ θ r => r • (cos θ, sin θ))
      (g := fun _ _ => sqrt r2)
      (dom := fun _ => Ioc (-RealScalar.pi) (RealScalar.pi)) := sorry_proof

theorem circle_sqrt_inverse (r2 : R) (h : 0 ≤ r2) :
    ParametricInverseAt
      (fun x : R×R => x.1^2 + x.2^2 - r2) 0
      (I := Bool)
      (p := fun _ x y => (x,y))
      (g := fun b x =>
        let y := sqrt (r2 - x^2)
        if b then y else -y)
      (dom := fun b =>
        let r := sqrt r2
        if b then
          Icc (-r) r
        else
          Ioo (-r) r) := sorry_proof
