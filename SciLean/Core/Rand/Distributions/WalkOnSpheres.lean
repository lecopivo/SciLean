import SciLean.Core.Rand.Rand
import SciLean.Core.Rand.Tactic
import SciLean.Core.FunctionTransformations
import SciLean.Core.Notation.CDeriv
import SciLean.Core.Notation.FwdDeriv

-- import Mathlib.MeasureTheory.Measure.Haar.Basic
-- import Mathlib.MeasureTheory.Constructions.Pi

import SciLean.Tactic.ConvInduction

open MeasureTheory

namespace SciLean

variable
  {R} [RealScalar R]
  {ι} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
  {X} [FinVec ι R X] [Module ℝ X] [MeasureSpace X]
  {Y} [SemiHilbert R Y] [Module ℝ Y]
  {U} [Vec R U] [Module ℝ U]
  {W} [Vec R W] [Module ℝ W]
  {α} [MeasurableSpace α]

set_default_scalar R

def sphere (x : X) (r : R) := {y : X // ‖y-x‖₂[R] = r}
def ball   (x : X) (r : R) := {y : X  | ‖y-x‖₂[R] < r}

instance (x : X) (r : R) : MeasureSpace (sphere x r) := sorry

#check ∫' (y : (sphere (0:X) (1:R))), y.1

def harmonic_function (u : X → Y) : Prop := ∀ x (r : R), u x = ∫' (y : sphere x r), u y.1

def poisson_function (f : X → Y) (u : X → Y) : Prop := ∀ x (r : R), u x = ∫' (y : sphere x r), u y.1 + ∫' y in ball x r, f y

theorem integral_to_unit_sphere (x : X) (r : R) (u : X → Y) :
    (∫' (x' : sphere x r), u x'.1)
    =
    r^2 • ∫' (x' : sphere (0:X) (1:R)), u (x + r • x'.1) := sorry_proof

#exit
variable
    {C : ℕ → Type} [∀ n, Vec R (C n)] [∀ n, MeasurableSpace (C n)]
    {D : ℕ → Type} [∀ n, MeasurableSpace (D n)]


-- This is true only for probability measures!!!!
-- for general measures it is true only for linear maps
open Measure in
@[rand_pull_E]
theorem pull_integral_nat_recOn (x₀ : C 0) (μ : (n : Nat) → Measure (D n))
    (f : (n : ℕ) → C n → D n → (C (n+1))) (hf : ∀ n d, IsAffineMap R (f n · d)) :
    Nat.recOn (motive := C)
      n
      x₀
      (fun n x => ∫' y', (f n x y') ∂(μ n))
    =
    ∫' y', y'
      ∂(Nat.recOn (motive:=fun n => Measure (C n)) n
         (dirac x₀)
         (fun n x =>
           Measure.bind x fun x' =>
           Measure.bind (μ n) fun y' =>
           dirac (f n x' y'))) := sorry
  -- induction n
  -- case zero => simp[mean]
  -- case succ n hn =>
  --   simp[hn,mean]
  --   conv => simp[rand_pull_E]
  --   conv =>
  --     lhs
  --     enter[1,2,x',1]
  --     unfold mean
  --     simp[pull_E_affine (f:=(f n · x')) (hf:=hf n x')]
  --   conv =>
  --     simp[rand_pull_E]
  --   rw[Rand.swap_bind]



--variable (φ : X → R) (φ' : X → X) (hφ : gradient φ = φ') (g : X → Y)

noncomputable
def harmonicRec (n : ℕ) (φ : X → R) (g : X → Y) (x : X) : Y :=
  match n with
  | 0 => g x
  | m+1 => ∫' (x' : sphere (0:X) (1:R)), harmonicRec m φ g (x + φ x • x'.1)


@[fun_prop]
theorem harmonicRec.arg_x.CDifferentiable_rule (n : ℕ)
    (φ : X → R) (g : X → Y)
    (hφ : CDifferentiable R φ) (hg : CDifferentiable R g) :
    CDifferentiable R (fun x : X => harmonicRec n φ g x) := by
  induction n <;> (simp[harmonicRec]; fun_prop)


-- set_option trace.Meta.Tactic.fun_trans true in
noncomputable
def harmonicRec.arg_x.cderiv (n : ℕ)
    (φ : X → R) (φ' : X → X → R) (g : X → Y) (g' : X → X → Y) :=
    (∂ x, harmonicRec n φ g x)
  rewrite_by
    assuming (hφ' : ∂ φ = φ') (hφ : CDifferentiable R φ)
             (hg' : ∂ g = g') (hg : CDifferentiable R g)
    induction n n' prev h
      . simp[harmonicRec]; fun_trans
      . simp[harmonicRec]
        fun_trans

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
      . simp[harmonicRec]
        rw[integral_fwdDeriv (hf:=by fun_prop)]
        enter [w,dw,1,x]

variable
  (n : ℕ)
  (φ : X → R) (g : X → Y)
  (hφ : CDifferentiable R φ) (hg : CDifferentiable R g)


variable [MeasurableSpace Y]


set_option pp.funBinderTypes true in
def walkOnSpheres (φ : X → R) (g : X → Y) (n : ℕ) (x : X) : Rand Y := do
  let f : Rand (X → Y) :=
    derive_random_approx
      (fun x => harmonicRec φ g n x)
    by
      induction n n' prev h
        . simp[harmonicRec]
        . simp[harmonicRec,h]
          simp[integral_lambda_push]
      rw[pull_integral_nat_recOn (R:=R) (x₀:=_) (μ:=_) (hf:=by fun_prop)]
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
