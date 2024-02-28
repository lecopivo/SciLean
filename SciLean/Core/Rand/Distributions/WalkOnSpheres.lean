import SciLean.Core.Rand.Rand
import SciLean.Core.Rand.Tactic
import SciLean.Core.Rand.Distributions.UniformI
import SciLean.Core.Rand.Distributions.Normal
import SciLean.Core.FunctionTransformations
import SciLean.Core.Notation.CDeriv
import SciLean.Core.Notation.FwdDeriv
import SciLean.Tactic.LSimp.LetNormalize

import SciLean.Core.FloatAsReal
import SciLean.Tactic.LetUtils
import SciLean.Tactic.LetEnter

import SciLean.Data.DataArray
import SciLean.Data.ArrayType.Algebra

-- import Mathlib.MeasureTheory.Measure.Haar.Basic
-- import Mathlib.MeasureTheory.Constructions.Pi

import SciLean.Tactic.ConvInduction

open MeasureTheory

namespace SciLean

-- Pretty printing of `Nat.recOn`
local syntax "rec_val" term ppLine "| " term " => " term ppLine "| " term ", " term " => "  term : term
@[local app_unexpander Nat.recOn]
def unexpandNatRecOn : Lean.PrettyPrinter.Unexpander
  | `($(_) $mot $n $base $succ) =>
    match succ with
    | `(fun ($m:ident : $Y:term) ($prev:ident : $P:term) $ys* => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => fun $ys* => $b)
    | `(fun $m:ident $prev:ident $ys* => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => fun $ys* => $b)
    | _ => throw ()
  | `($(_) $n $base $succ) =>
    match succ with
    | `(fun ($m:ident : $Y:term) ($prev:ident : $P:term) $ys* => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => fun $ys* => $b)
    | `(fun $m:ident $prev:ident $ys* => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => fun $ys* => $b)
    | _ => throw ()
  | _ => throw ()

@[local app_unexpander Nat.rec]
def unexpandNatRec : Lean.PrettyPrinter.Unexpander
  | `($(_) $mot $base $succ $n) =>
    match succ with
    | `(fun ($m:ident : $Y:term) ($prev:ident : $P:term) $ys* => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => fun $ys* => $b)
    | `(fun $m:ident $prev:ident $ys* => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => fun $ys* => $b)
    | _ => throw ()
  | `($(_) $base $succ $n) =>
    match succ with
    | `(fun ($m:ident : $Y:term) ($prev:ident : $P:term) $ys* => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => fun $ys* => $b)
    | `(fun $m:ident $prev:ident $ys* => $b) =>
      `(rec_val $n | 0 => $base | $m+1, $prev => fun $ys* => $b)
    | _ => throw ()
  | _ => throw ()


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

instance : LawfulIndexType (Fin n) where
  toFin_leftInv  := by intro _; rfl
  toFin_rightInv := by intro _; rfl

section Rand

@[coe]
def _root_.SciLean.Scalar.ofENNReal {R} [RealScalar R] (x : ENNReal) : R :=
  Scalar.ofReal R x.toReal

@[coe]
noncomputable
def _root_.SciLean.Scalar.toENNReal {R} [RealScalar R] (x : R) : ENNReal :=
  .ofReal (Scalar.toReal R x)

@[simp]
theorem _root_.SciLean.Scalar.oftoENNReal {R} [RealScalar R] (x : R) :
    Scalar.ofENNReal (Scalar.toENNReal x)
    =
    abs x := sorry_proof

variable
  {R} [RealScalar R]
  {ι} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
  {X} [FinVec ι R X] [Module ℝ X] [MeasureSpace X]

class UniformRand (X : Type _) where
  uniform : Rand X

def uniform (X : Type _) [UniformRand X] : Rand X := UniformRand.uniform

abbrev π : Float := RealScalar.pi


open Prob Scalar in
instance (x : Vec3) (r : Float) : UniformRand (sphere x r) where
  uniform := {
    spec := erase sorry
    rand := Rand.rand <| do
      let z := 2*(← uniformI Float) - 1
      let θ := 2*π*(← uniformI Float)
      let r := sqrt (1 - z*z)
      pure ⟨v[r*cos θ, r*sin θ, z], sorry_proof⟩}


theorem uniform_sphere_density (x : Vec3) (r : Float) (y : sphere x r) :
  (volume : Measure (sphere x r)).rnDeriv (uniform (sphere x r)).ℙ y
  =
  Scalar.toENNReal (4.0*π) := sorry_proof

@[simp]
theorem uniform_sphere_density' (x : Vec3) (r : Float) (y : sphere x r) :
  Scalar.ofENNReal ((volume : Measure (sphere x r)).rnDeriv (uniform (sphere x r)).ℙ y)
  =
  4.0*π := sorry_proof


set_default_scalar Float

#eval show IO Unit from do
  let x ← (uniform (sphere (0:Vec3) 1.0)).get
  IO.println x
  IO.println (‖x.1‖₂)


noncomputable
def _root_.MeasureTheory.Measure.rdensity {α} [MeasurableSpace α] (R : Type _) [RealScalar R] (μ ν : Measure α) : α → R :=
  fun x => Scalar.ofReal R (μ.rnDeriv ν x).toReal

attribute [pp_dot] Rand.ℙ Rand.E

theorem integral_as_uniform_E (R) [RealScalar R] {Y} [AddCommGroup Y] [Module R Y] [Module ℝ Y]
    (f : X → Y) (μ : Measure X) [UniformRand X] :
    ∫' (x : X), f x ∂μ
    =

    (uniform X).E (fun x =>
      let density :=(Scalar.ofENNReal (R:=R) (μ.rnDeriv (uniform X).ℙ x))
      density • f x) := sorry

theorem integral_as_uniform_E' {Y} [AddCommGroup Y] [Module ℝ Y]
    (f : X → Y) (μ : Measure X) [UniformRand X] :
    ∫' (x : X), f x ∂μ
    =
    (uniform X).E (fun x =>
      let density := (μ.rnDeriv (uniform X).ℙ x)
      density.toReal • f x) := sorry


end Rand

attribute [coe] Scalar.ofReal
theorem normalize_smul {X} [SMul ℝ X]
  (R) [RealScalar R] [SMul R X] [IsScalarTower ℝ R X]
  (r : ℝ) (x : X) :
  r • x = (Scalar.ofReal R r) • x := sorry_proof



variable {Y : Type} [SemiHilbert Float Y] [Module ℝ Y] [IsScalarTower ℝ Float Y]
set_default_scalar Float




noncomputable
def harmonicRec (n : ℕ) (φ : Vec3 → Float) (g : Vec3 → Y) (x : Vec3) : Y :=
  match n with
  | 0 => g x
  | m+1 => (4*π)⁻¹ • ∫' (x' : sphere (0:Vec3) 1.0), harmonicRec m φ g (x + φ x • x'.1)




set_option pp.funBinderTypes true in
def walkOnSpheres (φ : Vec3 → Float) (g : Vec3 → Y) (n : ℕ) (x : Vec3) : Rand Y := do
  let f : Rand (Vec3 → Y) :=
    derive_random_approx
      (fun x => harmonicRec n φ g x)
    by
      induction n n' prev h
        . simp[harmonicRec]
        . simp[harmonicRec,h]
          simp only [smul_push,cintegral.arg_f.push_lambda]
          rw[integral_as_uniform_E Float]
      rw[pull_E_nat_recOn (x₀:=_) (r:=_) (hf:=by fun_prop)]
      let_unfold density
      simp (config:={zeta:=false})
  let f' ← f
  pure (f' x)


def walkOnSpheres.manualImpl (φ : Vec3 → Float) (g : Vec3 → Y) (n : ℕ) (x : Vec3) : Rand Y := do
  match n with
  | 0 => pure (g x)
  | n+1 => do
    let y ← (uniform (sphere (0:Vec3) 1.0))
    walkOnSpheres.manualImpl φ g n (x + φ x • y)


def _root_.SciLean.Vec3.add (u v : Vec3) : Vec3 := ⟨u.x+v.x, u.y+v.y, u.z+v.z⟩
def _root_.SciLean.Vec3.smul (s : Float) (u : Vec3) : Vec3 := ⟨s * u.x, s * u.y, s * u.z⟩

def walkOnSpheres.manualImplV2 (φ : Vec3 → Float) (g : Vec3 → Y) (n : ℕ) (x : Vec3) : Rand Y := do
  match n with
  | 0 => pure (g x)
  | n+1 => do
    let y ← (uniform (sphere (0:Vec3) 1.0))
    walkOnSpheres.manualImpl φ g n (x.add (Vec3.smul (φ x) y))


-- | Rand.mean
--     (rec_val n
--       | 0 => pure fun (x : Vec3) => g x
--       | n + 1, x => fun => do
--       let x' ← x
--       let y' ← uniform ↑(sphere 0 1.0)
--       pure
--           (↑(Measure.rnDeriv volume (uniform ↑(sphere 0 1.0)).ℙ y') • fun (x : Vec3) => (π⁻¹ * 4⁻¹) • x' (x + φ x • ↑y')))



#exit
#check Nat

def φ (x : Vec3) : Float := |‖x‖₂ - 1|
def g (x : Vec3) : Float := if ‖x‖₂² < 1.01 then 1 else 0

#eval φ v[1,0,0]

#eval Prob.print_mean_variance (walkOnSpheres φ g 10 v[3,0,0]) 1000 ""



@[fun_prop]
theorem harmonicRec.arg_x.CDifferentiable_rule (n : ℕ)
    (φ : Vec3 → Float) (g : Vec3 → Y)
    (hφ : CDifferentiable Float φ) (hg : CDifferentiable Float g) :
    CDifferentiable Float (fun x : Vec3 => harmonicRec n φ g x) := by
  induction n <;> (simp[harmonicRec]; fun_prop)


noncomputable
def harmonicRec.arg_x.cderiv (n : ℕ)
    (φ : Vec3 → Float) (φ' : Vec3 → Vec3 → Float) (g : Vec3 → Y) (g' : Vec3 → Vec3 → Y) :=
    (∂ x, harmonicRec n φ g x)
  rewrite_by
    assuming (hφ' : ∂ φ = φ') (hφ : CDifferentiable Float φ)
             (hg' : ∂ g = g') (hg : CDifferentiable Float g)
    induction n n' du h
      . simp[harmonicRec]; fun_trans
      . simp only [harmonicRec]; fun_trans only [ftrans_simp]

noncomputable
def harmonicRec.arg_x.fwdDeriv (n : ℕ)
    (φ : Vec3 → Float) (φ' : Vec3 → Vec3 → Float×Float)
    (g : Vec3 → Y) (g' : Vec3 → Vec3 → Y×Y) :=
    (∂> x, harmonicRec n φ g x)
  rewrite_by
    assuming (hφ' : ∂> φ = φ') (hφ : CDifferentiable Float φ)
             (hg' : ∂> g = g') (hg : CDifferentiable Float g)
    induction n n' du h
      . simp[harmonicRec]; fun_trans
      . simp[harmonicRec];
        enter[x];
        -- simp (config:={zeta:=false}) only [smul_push]
        fun_trans (config:= {zeta:=false,singlePass:=true}) only [Tactic.let_normalize,ftrans_simp]
