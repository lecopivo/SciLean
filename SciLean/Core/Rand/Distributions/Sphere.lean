import SciLean.Core.Rand.Rand
import SciLean.Data.DataArray
import SciLean.Data.ArrayType.Algebra
import SciLean.Core.FloatAsReal
import SciLean.Core.FunctionTransformations
import SciLean.Core.Notation.CDeriv
import SciLean.Core.Notation.FwdDeriv
import SciLean.Tactic.LSimp.LetNormalize
import SciLean.Tactic.LetNormalize
import SciLean.Tactic.LetNormalize2
-- import Mathlib.Tactic.LiftLets
import SciLean.Util.Profile


open MeasureTheory

namespace SciLean


section Geometry

variable
  {R} [RealScalar R]
  {ι} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
  {X} [FinVec ι R X] [Module ℝ X] [MeasureSpace X]

def sphere (x : X) (r : R) := {y : X | ‖y-x‖₂[R] = r}
def ball   (x : X) (r : R) := {y : X | ‖y-x‖₂[R] < r}

1instance (x : X) (r : R) : MeasureSpace (sphere x r) := sorry
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
  let s := (xnorm / ynorm)
  s • y


variable (x dx v : Vec3) (s : Float)

#check Lean.Meta.lambdaTelescope


open Lean Meta
simproc_decl lift_lets_simproc (_) := fun e => do
  let E ← inferType e
  if (← Meta.isClass? E).isSome then return .continue
  let e ← e.liftLets2 (fun xs b => do
      if xs.size ≠ 0
      then mkLetFVars xs (← Simp.dsimp b)
      else pure b) {}
  return .visit {expr:=e}


open Lean Meta
simproc_decl post_check (_) := fun e => do
    IO.println s!"running post on  {← ppExpr e}"
    let e' ← Simp.dsimp e
    return .visit {expr := e'}


variable (f : Vec3 → Vec3) (hf : CDifferentiable Float f)

macro "autodiff" : conv =>
  `(conv| fun_trans (config:={zeta:=false,singlePass:=true}) (disch:=sorry) only [ftrans_simp,lift_lets_simproc])

-- set_option trace.Meta.Tactic.fun_trans true in
-- set_option trace.Meta.Tactic.fun_prop true
#check (∂> x' : Vec3, mkSphereMap' f x')
  rewrite_by
    unfold mkSphereMap'
    conv =>
      enter [x]
      autodiff
      autodiff


set_option trace.Meta.Tactic.fun_trans true in
#check (fwdDeriv Float fun x' : Vec3 =>
      let x' := (x',x').1
      x')
  rewrite_by
    enter [x]
    autodiff
    autodiff





-- set_option trace.Meta.Tactic.fun_trans true in
-- set_option trace.Meta.Tactic.fun_trans.rewrite true in
#check (∂ x' : Vec3,
      let x' := s • x'
      x')
  rewrite_by
    autodiff


#check (∂ x' : Vec3,
      let x' := s • x'
      let y := (fun x => v + x) x';
      y)
  rewrite_by
    autodiff

#check (∂ x' : Vec3,
      let x' := s • x'
      let y := (fun x => v + s • x + x) x';
      y)
  rewrite_by
    autodiff

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
  det3 (fun dx => ∂ x':=x;dx, mkSphereMap' f x')

def elongate (s : Float) (v : Vec3) (x : Vec3) : Vec3 :=
  ((s - 1) * ⟪v, x⟫[Float]) • v + x


-- #profile_this_file

set_option profiler true

noncomputable
def elongateDensity (s : Float) (v : Vec3) (x : Vec3) : Float := (sphereMapDensity (elongate s v) x)
  rewrite_by
    unfold sphereMapDensity elongate mkSphereMap'

    -- simp (config:={zeta:=false,singlePass:=true}) (disch:=sorry) only
    --   [↓Mathlib.Meta.FunTrans.fun_trans_simproc,↓Tactic.let_normalize,lift_lets_simproc, ftrans_simp]

    autodiff
    autodiff
    simp (config:={zeta:=false}) only [lift_lets_simproc]
    -- simp (config:={zeta:=false}) only [lift_lets_simproc]
    -- simp (config:={zeta:=false}) [Tactic.let_normalize]
    -- let_normalize
    -- simp (config:={zeta:=false,proj:=false,singlePass:=true}) only [ftrans_simp]
    -- let_normalize

    --  simp (config:={zeta:=false,proj:=false,singlePass:=true}) only [ftrans_simp,Tactic.let_normalize]

#check Nat
