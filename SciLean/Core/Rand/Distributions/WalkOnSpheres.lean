import SciLean.Core.Rand.Rand
import SciLean.Core.Rand.Tactic
import SciLean.Core.Rand.Distributions.Uniform
import SciLean.Core.Rand.Distributions.Sphere

import SciLean.Core.FunctionTransformations
import SciLean.Core.Notation.CDeriv
import SciLean.Core.Notation.FwdDeriv

import SciLean.Core.FloatAsReal
import SciLean.Tactic.LetUtils
import SciLean.Tactic.LetEnter
import SciLean.Util.RecVal

import SciLean.Tactic.ConvInduction

open MeasureTheory

namespace SciLean

variable {Y : Type} [SemiHilbert Float Y] [Module ℝ Y] [IsScalarTower ℝ Float Y]
set_default_scalar Float


def pi' := 3.14159265359

open RealScalar in
noncomputable
def harmonicRec (n : ℕ) (φ : Vec3 → Float) (g : Vec3 → Y) (x : Vec3) : Y :=
  match n with
  | 0 => g x
  | m+1 => (4*(pi':Float))⁻¹ • ∫' (x' : sphere (0:Vec3) (1:Float)), harmonicRec m φ g (x + φ x • x'.1)


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
      simp (config:={zeta:=false})
  let f' ← f
  pure (f' x)


@[fun_prop]
theorem harmonicRec.arg_x.CDifferentiable_rule (n : ℕ)
    (φ : Vec3 → Float) (g : Vec3 → Y)
    (hφ : CDifferentiable Float φ) (hg : CDifferentiable Float g) :
    CDifferentiable Float (fun x : Vec3 => harmonicRec n φ g x) := by
  induction n <;> (simp[harmonicRec]; fun_prop)

variable {W} [Vec Float W]

-- set_option pp.notation false
noncomputable
def harmonicRec_fwdDeriv (n : ℕ)
    (φ : Vec3 → Float) (φ' : Vec3 → Vec3 → Float×Float)
    (g : Vec3 → Y) (g' : Vec3 → Vec3 → Y×Y) : Vec3 → Vec3 → Y×Y :=
    (∂> x, harmonicRec n φ g x)
  rewrite_by
    assuming (hφ' : ∂> φ = φ') (hφ : CDifferentiable Float φ)
             (hg' : ∂> g = g') (hg : CDifferentiable Float g)
    induction n n' du h
      . simp[harmonicRec]; autodiff
      . simp[harmonicRec];
        simp only [smul_push]
        autodiff; autodiff


def harmonicRec.arg_x.fwdDeriv_randApprox (n : ℕ)
    (φ : Vec3 → Float) (φ' : Vec3 → Vec3 → Float×Float)
    (g : Vec3 → Y) (g' : Vec3 → Vec3 → Y×Y)
    (x dx : Vec3) : Rand (Y×Y) := do
  let f : Rand (Vec3 → Vec3 → Y×Y) :=
    derive_random_approx
      (fun x dx => harmonicRec_fwdDeriv n φ φ' g g' x dx)
    by
      unfold harmonicRec_fwdDeriv
      conv =>
        pattern (fun _ _ _ _ => cintegral _ _)
        enter [n,du]
        conv =>
          conv => enter [x];rw[cintegral.arg_f.push_lambda]
          rw[cintegral.arg_f.push_lambda]
        rw[integral_as_uniform_E Float]
      rw[pull_E_nat_recOn (x₀:=_) (r:=_) (hf:=by fun_prop)]
      simp (config:={zeta:=false})
  let f' ← f
  pure (f' x dx)



noncomputable
def harmonicRec_fwdDeriv2 (n : ℕ)
    (φ : W → Vec3 → Float) (φ' : W → Vec3 → W → Vec3 → Float×Float)
    (g : Vec3 → Y)  (x : Vec3) :=
    (∂> w, harmonicRec n (φ w) g x)
  rewrite_by
    assuming (hφ' : (fwdDeriv Float (fun (wx : W×Vec3) => φ wx.1 wx.2)) = fun wx dwx => φ' wx.1 wx.2 dwx.1 dwx.2)
             (hφ : CDifferentiable Float (fun (w,x) => φ w x))
    induction n n' du h
      . simp[harmonicRec]; autodiff
      . simp[harmonicRec];
        autodiff; autodiff
