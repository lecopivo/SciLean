import SciLean.Core.Distribution.ParametricDistribDeriv
import SciLean.Core.Distribution.SurfaceDirac
import SciLean.Core.Integral.Substitution
import SciLean.Core.Integral.ParametricInverse
import SciLean.Core.Integral.Frontier
import SciLean.Core

import SciLean.Util.RewriteBy

open MeasureTheory

namespace SciLean

variable
  {R} [RealScalar R]
  {W} [SemiHilbert R W]
  {X} [SemiHilbert R X]
  {Y} [SemiHilbert R Y] -- [Module ℝ Y]
  {Z} [SemiHilbert R Z] -- [Module ℝ Z]

set_default_scalar R

variable [MeasureSpace R] -- [Module ℝ R]

structure BungeeParams where
  (l₁ l₂ k₁ k₂ α : R)

def g : R := 9.81

def bungeeTension (l₁ l₂ k₁ k₂ α : R) (bungeeLength : R) : R :=
  let x := bungeeLength
  let x₁ := k₂ / (k₁ + k₂) * x
  let x₂ := k₁ / (k₁ + k₂) * x
  if x₁ ≤ l₁ then
    if x₂ ≤ l₂ then
      k₁ * x₁ + k₂ * x₂
    else
      α * k₂ * l₂ + k₁ * (x₁ + x₂ - l₂)
  else
    if x₂ ≤ l₂ then
      α * k₁ * l₁ + k₂ * (x₁ + x₂ - l₂)
    else
      g
  -- match (x₁ ≤ l₁ : Bool), (x₂ ≤ l₂ : Bool) with
  -- |  true,  true => k₁ * x₁ + k₂ * x₂
  -- |  true, false => α * k₂ * l₂ + k₁ * (x₁ + x₂ - l₂)
  -- | false,  true => α * k₁ * l₁ + k₂ * (x₁ + x₂ - l₂)
  -- | false, false => g

open Set

noncomputable
def velocity (m : R) (l₁ l₂ k₁ k₂ α : R) (bungeeLength : R) : R :=
  (Scalar.sqrt (2 * ∫' z in Ioo 1 bungeeLength, (g - bungeeTension l₁ l₂ k₁ k₂ α z / m)))


noncomputable
def timeToFall (m : R) (l₁ l₂ k₁ k₂ α : R) (height : R) : R :=
  -- ∫' x in Ioo 1 height, 2 * ∫' z in Ioo 0 x, (g - bungeeTension l₁ l₂ k₁ k₂ α z / m)
  ∫' (x,z) in {((x',z') : R×R) | 1 ≤ x' ∧ x' ≤ height ∧ 0 ≤ z' ∧ z' ≤ x'}, (g - bungeeTension l₁ l₂ k₁ k₂ α z / m)

noncomputable
def timeToFall' (m : R) (l₁ l₂ k₁ k₂ α : R) (height : R) : R :=
  ∫' x in Ioo 1 height, 2 * ∫' z in Ioo 0 x, (g - bungeeTension l₁ l₂ k₁ k₂ α z / m)


noncomputable
def objective (m : R) (l₁ l₂ k₁ k₂ α : R) (height : R) : R :=
  let t := timeToFall m l₁ l₂ k₁ k₂ α height
  let a := g - bungeeTension l₁ l₂ k₁ k₂ α 1 / m
  t + a

def constraint (m : R) (l₁ l₂ k₁ k₂ α : R) (height : R) := velocity m l₁ l₂ k₁ k₂ α 1 = 0

variable (m l₁ l₂ k₁ k₂ α : R) (x : R)

#check (∂ l, velocity m l l₂ k₁ k₂ α x)
  rewrite_by
    unfold velocity bungeeTension
    fun_trans (config:={zeta:=false})

variable (x : R)

set_option profiler true

-- set_option trace.Meta.Tactic.fun_prop true in
-- example : CDifferentiable R (fun l => ∫' z in Ioo 1 x, bungeeTension l l₂ k₁ k₂ α z) := by
--   simp only [bungeeTension]
--   simp (config := {zeta:=false}) only [ftrans_simp,bungeeTension]
--   fun_prop (disch:=sorry)

attribute [ftrans_simp] FiniteDimensional.finrank_self FiniteDimensional.finrank_prod mem_setOf_eq not_le ite_mul mul_ite mul_neg mul_one

-- set_option pp.notation false in
-- set_option trace.Meta.Tactic.fun_trans true in
-- set_option trace.Meta.Tactic.fun_trans.step true in
-- set_option trace.Meta.Tactic.simp.rewrite true in
-- set_option trace.Meta.Tactic.simp.unify true in
#check (cderiv R fun l => ∫' z, bungeeTension l l₂ k₁ k₂ α z)
  rewrite_by
    unfold bungeeTension
    autodiff
    unfold scalarGradient
    autodiff
    fun_trans (config:={zeta:=false}) (disch:=sorry) only [ftrans_simp, scalarGradient]


@[simp, ftrans_simp]
theorem ite_apply {α β : Type _} {c : Prop} [Decidable c] (t e : α → β) (x : α) :
    (ite c t e) x = ite c (t x) (e x) := by if h : c then simp[h] else simp[h]


theorem t1 [MeasurableSpace X] (A : Set X) (φ ψ : X → R) (f g : X → R) (μ : Measure X) :
    ∫' x in A, (if φ x < ψ x then f x else g x) ∂μ
    =
    ∫' x in A ∩ {x' | φ x' < ψ x'}, f x ∂μ
    +
    ∫' x in A ∩ {x' | ψ x' ≤ φ x'}, g x ∂μ := sorry_proof

theorem t2 [MeasurableSpace X] (φ ψ : X → R) (f g : X → R) (μ : Measure X) :
    ∫' x, (if φ x < ψ x then f x else g x) ∂μ
    =
    (∫' x in {x' | φ x' < ψ x'}, f x ∂μ)
    +
    ∫' x in {x' | ψ x' ≤ φ x'}, g x ∂μ := sorry_proof

theorem t3 [MeasurableSpace X] (c : X → Prop) [∀ x, Decidable (c x)] (f g : X → R) (μ : Measure X) :
    ∫' x, (if c x then f x else g x) ∂μ
    =
    (∫' x in {x' | c x'}, f x ∂μ)
    +
    (∫' x in {x' | ¬(c x')}, g x ∂μ) := sorry_proof


theorem t4 [MeasurableSpace X] (A : Set X) (c : X → Prop) [∀ x, Decidable (c x)] (f g : X → R) (μ : Measure X) :
    ∫' x in A, (if c x then f x else g x) ∂μ
    =
    (∫' x in {x' | c x'} ∩ A, f x ∂μ)
    +
    (∫' x in {x' | ¬(c x')} ∩ A, g x ∂μ) := sorry_proof

theorem t3' [MeasurableSpace X] (c : Prop) [Decidable c] (f g : X → R) (μ : Measure X) :
    ∫' x, (if c then f x else g x) ∂μ
    =
    if c then
      ∫' x, f x ∂μ
    else
      ∫' x, g x ∂μ := sorry_proof


theorem t4' [MeasurableSpace X] (A : Set X) (c : Prop) [Decidable c] (f g : X → R) (μ : Measure X) :
    ∫' x in A, (if c then f x else g x) ∂μ
    =
    if c then
      ∫' x in A, f x ∂μ
    else
      ∫' x in A, g x ∂μ := sorry_proof


theorem set_inter {α} (P Q : α → Prop) : {x | P x} ∩ {x | Q x} = {x | P x ∧ Q x} := by aesop



-- open Lean Meta in
-- simproc hihi' (Distribution.extAction _ _) := fun e => do

--   -- let φ := e.appArg!
--   -- let T := e.appFn!.appArg!.appArg!.appFn!.appArg!
--   IO.println s!"extAction simproc simplification with distribution {← ppExpr e}"

--   return .continue

theorem split_integral {X} {Y} [MeasureSpace X] [MeasureSpace Y] (f : X×Y → R) :
    ∫' (xy : X×Y), f xy = ∫' x, ∫' y, f (x,y) := sorry_proof

#check SciLean.toDistribution.arg_f.parDistribDeriv_rule
#check (cderiv R fun l => timeToFall m l l₂ k₁ k₂ α x)
  rewrite_by
    unfold timeToFall bungeeTension
    autodiff
    unfold scalarGradient; autodiff
    simp (config:={zeta:=false}) only [action_push, ftrans_simp]
    simp (config:={zeta:=false}) only [t3',t4',t1, t2, t4, ftrans_simp,set_inter]


l₁
set_option pp.funBinderTypes true in
set_option trace.Meta.Tactic.fun_trans true in
set_option trace.Meta.Tactic.simp.unify true in
set_option trace.Meta.Tactic.simp.discharge true in
#check (cderiv R fun l => timeToFall' m l l₂ k₁ k₂ α x)
  rewrite_by
    unfold timeToFall' bungeeTension
    fun_trans only
    unfold scalarGradient; autodiff
    simp only [ftrans_simp, action_push, Distribution.mk_extAction_simproc, split_integral]
    simp (config:={zeta:=false}) only [t3',t4',t1, t2, t4, ftrans_simp,set_inter]
    simp only [t3, ftrans_simp]
    -- rw [Distribution.mk_extAction (X:=R)]
    -- unfold scalarGradient
    -- autodiff
    -- simp only [Distribution.action_iteD,ftrans_simp]




#exit
#check split_integral_over_set_of_ite


#check SciLean.split_integral_over_set_of_ite


#check ge_iff_le


#check HAdd.hAdd.arg_a0a1.cderiv_rule


#check {(x, z) | 1 ≤ x ∧ x ≤ u ∧ 0 ≤ z ∧ z ≤ x}
