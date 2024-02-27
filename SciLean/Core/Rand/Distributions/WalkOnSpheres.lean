import SciLean.Core.Rand.Rand
import SciLean.Core.Rand.Tactic
import SciLean.Core.FunctionTransformations
import SciLean.Core.Notation.CDeriv
import SciLean.Core.Notation.FwdDeriv
import SciLean.Tactic.LSimp.LetNormalize

import SciLean.Data.DataArray

-- import Mathlib.MeasureTheory.Measure.Haar.Basic
-- import Mathlib.MeasureTheory.Constructions.Pi

import SciLean.Tactic.ConvInduction

open MeasureTheory

namespace SciLean

variable
  {R} [RealScalar R]
  {ι} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
  {X} [FinVec ι R X] [Module ℝ X] [MeasureSpace X]
  {Y} [SemiHilbert R Y] [Module ℝ Y] [IsScalarTower ℝ R Y]
  {U} [Vec R U] [Module ℝ U]
  {W} [Vec R W] [Module ℝ W]
  {α} [MeasurableSpace α]

set_default_scalar R

def sphere (x : X) (r : R) := {y : X // ‖y-x‖₂[R] = r}
def ball   (x : X) (r : R) := {y : X  | ‖y-x‖₂[R] < r}

abbrev π : R := RealScalar.pi

variable [PlainDataType R]
#check DataArrayN R (Fin 3)

#check R^[Fin 3]

instance (x : X) (r : R) : MeasureSpace (sphere x r) := sorry

#check ∫' (y : (sphere (0:X) (1:R))), y.1

def harmonic_function (u : X → Y) : Prop := ∀ x (r : R), u x = ∫' (y : sphere x r), u y.1

theorem integral_to_unit_sphere (x : X) (r : R) (u : X → Y) :
    (∫' (x' : sphere x r), u x'.1)
    =
    r^2 • ∫' (x' : sphere (0:X) (1:R)), u (x + r • x'.1) := sorry_proof


noncomputable
def harmonicRec (n : ℕ) (φ : X → R) (g : X → Y) (x : X) : Y :=
  match n with
  | 0 => g x
  | m+1 => (4*π:R)⁻¹ • ∫' (x' : sphere (0:X) (1:R)), harmonicRec m φ g (x + φ x • x'.1)


@[fun_prop]
theorem harmonicRec.arg_x.CDifferentiable_rule (n : ℕ)
    (φ : X → R) (g : X → Y)
    (hφ : CDifferentiable R φ) (hg : CDifferentiable R g) :
    CDifferentiable R (fun x : X => harmonicRec n φ g x) := by
  induction n <;> (simp[harmonicRec]; fun_prop)


set_option trace.Meta.Tactic.fun_trans true in

noncomputable
def harmonicRec.arg_x.cderiv (n : ℕ)
    (φ : X → R) (φ' : X → X → R) (g : X → Y) (g' : X → X → Y) :=
    (∂ x, harmonicRec n φ g x)
  rewrite_by
    assuming (hφ' : ∂ φ = φ') (hφ : CDifferentiable R φ)
             (hg' : ∂ g = g') (hg : CDifferentiable R g)
    induction n n' du h
      . simp[harmonicRec]; fun_trans
      . simp only [harmonicRec]; fun_trans only [ftrans_simp]

-- set_option trace.Meta.Tactic.fun_trans true in
noncomputable
def harmonicRec.arg_x.fwdDeriv (n : ℕ)
    (φ : X → R) (φ' : X → X → R×R) (g : X → Y) (g' : X → X → Y×Y) :=
    (∂> x, harmonicRec n φ g x)
  rewrite_by
    assuming (hφ' : ∂> φ = φ') (hφ : CDifferentiable R φ)
             (hg' : ∂> g = g') (hg : CDifferentiable R g)
    induction n n' prev h
      . simp[harmonicRec]; fun_trans
      . simp[harmonicRec]; fun_trans

variable
  (n : ℕ)
  (φ : X → R) (g : X → Y)
  (hφ : CDifferentiable R φ) (hg : CDifferentiable R g)

variable [MeasurableSpace Y]


class UniformRand (X : Type _) where
  uniform : Rand X

instance [FinVec ι R X] (x : X) (r : R) : UniformRand (sphere x r) where
  uniform := sorry

export UniformRand (uniform)

#check UniformRand.uniform.ℙ
#check volume

-- todo: scale by density!!!
theorem integral_as_uniform_E {Y} [AddCommGroup Y] [Module ℝ Y] -- todo: change to locally convex space
    (f : X → Y) [UniformRand X] :
    ∫' (x : X), f x = uniform.E f := sorry

set_option pp.funBinderTypes true in
def walkOnSpheres (φ : X → R) (g : X → Y) (n : ℕ) (x : X) : Rand Y := do
  let f : Rand (X → Y) :=
    derive_random_approx
      (fun x => harmonicRec n φ g x)
    by
      induction n n' prev h
        . simp[harmonicRec]
        . simp[harmonicRec,h]
          simp only [smul_push,cintegral.arg_f.push_lambda]
          rw[integral_as_uniform_E]
      rw[pull_E_nat_recOn (x₀:=_) (r:=_) (hf:=by fun_prop)]
  let f' ← f
  pure (f' x)

variable (u : X → Y) (φ : X → R) (hu : CDifferentiable R u) (hφ : CDifferentiable R φ)

#check SciLean.HSMul.hSMul.arg_a0a1.CDifferentiable_rule

example : CDifferentiable R fun (w4w5 : R × Y) => w4w5.1 • w4w5.2 := by fun_prop

set_option pp.funBinderTypes true in

set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.simp.unify true in
#check (cderiv R fun x => ∫' (x' : sphere (0:X) (1:R)), u (x + φ x • x'.1)) rewrite_by
  enter [x,dx]
  rw[integral_cderiv (hf:=by fun_prop)]
  fun_trans -- (setq lean4-info--goals [])


variable (n : Nat)
#check (cderiv R (fun x : X => harmonicRec φ g n x)) rewrite_by
  induction n n' prev h
    . simp [harmonicRec]
    . simp [harmonicRec,h]
      rw[integral_cderiv (hf:=by sorry)]
      fun_trans (disch:=sorry) -- (setq lean4-info--goals [])




-- #check volume (Metric.sphere x 1)
-- #check @volume _ (borel (Metric.sphere x 1))
-- #check @volume _ (borel (Metric.ball x 1))

-- #synth MeasurableSpace (Metric.ball x (1 :ℝ))
-- #synth MeasurableSpace (Metric.sphere x (1 :ℝ))
-- #synth MeasureSpace (Metric.sphere x (1 :ℝ))
