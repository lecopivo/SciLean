import SciLean.Core.FloatAsReal
import SciLean.Core.FunctionTransformations
import SciLean.Core.Notation.CDeriv
import SciLean.Core.Notation.FwdDeriv
import SciLean.Core.Rand.Rand
import SciLean.Core.Rand.Distributions.Uniform
import SciLean.Data.ArrayType
import SciLean.Data.DataArray
import SciLean.Tactic.Autodiff


open MeasureTheory

namespace SciLean


section Geometry

variable
  {R} [RealScalar R]
  {ι} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
  {X} [FinVec ι R X] [Module ℝ X] [MeasureSpace X]

def sphere (x : X) (r : R) := {y : X // ‖y-x‖₂[R] = r}
def ball   (x : X) (r : R) := {y : X | ‖y-x‖₂[R] < r}

instance (x : X) (r : R) : MeasureSpace (sphere x r) := sorry
instance (x : X) (r : R) [ToString X] : ToString (sphere x r) := ⟨fun x => toString x.1⟩


open RealScalar in
@[simp, ftrans_simp]
theorem sphere_volume (x : X) (r : R) :
   volume (Set.univ : Set (sphere x r))
   =
   Scalar.toENNReal (4 * pi * r^(2:Nat)) := sorry_proof


end Geometry


open Rand Scalar RealScalar in
instance (x : Vec3) (r : Float) : UniformRand (sphere x r) where
  uniform := {
    spec := erase ⟨fun φ => φ ⟨v[1,0,0],sorry_proof⟩⟩
    rand := Rand.rand <| do
      let z := 2*(← uniformI Float) - 1
      let θ := 2*pi*(← uniformI Float)
      let r := sqrt (1 - z*z)
      pure ⟨v[r*cos θ, r*sin θ, z], sorry_proof⟩}

open RealScalar in
@[simp, ftrans_simp]
theorem uniform_sphere_density (x : Vec3) (r : Float) :
  (volume : Measure (sphere x r)).rnDeriv (uniform (sphere x r)).ℙ
  =
  fun y => ENNReal.ofReal <| Scalar.toReal Float (4*pi*r^2) := sorry_proof


def mkSphereMap (f : Vec3 → Vec3) (x : Vec3) : Vec3 :=
  -- let xnorm := ‖x‖₂[Float]
  let y := f x
  let ynorm := ‖y‖₂[Float]
  ynorm⁻¹ • y

/-- On sphere this is identical to `mkSphereMap` but the jacobian of this map is equal to the
  two dimensional jacobian of `mkSphereMap f : S² → S²` which we need to compute as -/
def mkSphereMap' (f : Vec3 → Vec3) (x : Vec3) : Vec3 :=
  let xnorm := ‖x‖₂[Float]
  let x' := (1/xnorm) • x
  let y := f x'
  let ynorm := ‖y‖₂[Float]
  let s := (xnorm / ynorm)
  s • y


set_default_scalar Float

noncomputable
def sphereMapDensity (f : Vec3 → Vec3) (x : Vec3) : Float :=
  det3 (fun dx => ∂ x':=x;dx, mkSphereMap' f x')

def elongate (s : Float) (v : Vec3) (x : Vec3) : Vec3 :=
  ((s - 1) * ⟪v, x⟫[Float]) • v + x

noncomputable
def elongateDensity (s : Float) (v : Vec3) (x : Vec3) : Float := (sphereMapDensity (elongate s v) x)
  rewrite_by
    unfold sphereMapDensity elongate mkSphereMap'
    autodiff
    autodiff
