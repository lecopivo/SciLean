import SciLean.Core.Rand.Rand
import SciLean.Data.DataArray
import SciLean.Data.ArrayType.Algebra
import SciLean.Core.FloatAsReal
import SciLean.Core.FunctionTransformations
import SciLean.Core.Notation.CDeriv
import SciLean.Core.Notation.FwdDeriv
import SciLean.Tactic.LSimp.LetNormalize
import SciLean.Tactic.LetNormalize

open MeasureTheory

namespace SciLean


section Geometry

variable
  {R} [RealScalar R]
  {ι} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
  {X} [FinVec ι R X] [Module ℝ X] [MeasureSpace X]

def sphere (x : X) (r : R) := {y : X | ‖y-x‖₂[R] = r}
def ball   (x : X) (r : R) := {y : X | ‖y-x‖₂[R] < r}

instance (x : X) (r : R) : MeasureSpace (sphere x r) := sorry
instance (x : X) (r : R) [ToString X] : ToString (sphere x r) := ⟨fun x => toString x.1⟩

end Geometry


#check Vec3


set_default_scalar Float


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
  (xnorm / ynorm) • y


def det2 (A : Vec2 → Vec2) : Float :=
  let u := A v[1,0]
  let v := A v[0,1]
  u.x * v.y - u.y * v.x

def det3 (A : Vec3 → Vec3) : Float :=
  let u := A v[1,0,0]
  let v := A v[0,1,0]
  let w := A v[0,0,1]
  u.x * (v.y * w.z - v.z * w.y)
  - u.y * (v.x * w.z - v.z * w.x)
  + u.z * (v.x * w.y - v.y * w.x)


noncomputable
def sphereMapDensity (f : Vec3 → Vec3) (x : Vec3) : Float :=
  let J := fun dx => ∂ x':=x;dx, mkSphereMap' f x'
  det3 J

def elongate (s : Float) (v : Vec3) (x : Vec3) : Vec3 :=
  ((s - 1) * ⟪v, x⟫[Float]) • v + x


def elongateDensity (s : Float) (v : Vec3) (x : Vec3) : Float := (sphereMapDensity (elongate s v) x)
  rewrite_by
    unfold sphereMapDensity elongate mkSphereMap'

    fun_trans (config:={zeta:=false,singlePass:=true}) (disch:=sorry) only
    let_normalize
    simp (config:={zeta:=false,proj:=false,singlePass:=true}) only [ftrans_simp]
    let_normalize

    --  simp (config:={zeta:=false,proj:=false,singlePass:=true}) only [ftrans_simp,Tactic.let_normalize]

#check Nat

#eval elongateDensity 2 v[1,0,0] v[0.5,0.5,0.5].normalize
#eval elongateDensity 10 v[1,0,0] v[1,0,0]
