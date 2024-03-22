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

attribute [ftrans_simp] FiniteDimensional.finrank_self

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

set_option trace.Meta.Tactic.fun_trans true in
#check (cderiv R fun l => timeToFall m l l₂ k₁ k₂ α x)
  rewrite_by
    unfold timeToFall bungeeTension
    autodiff
    unfold scalarGradient
    autodiff



set_option trace.Meta.Tactic.fun_trans true in
#check (cderiv R fun l => timeToFall' m l l₂ k₁ k₂ α x)
  rewrite_by
    unfold timeToFall' bungeeTension
    autodiff
    unfold scalarGradient
    autodiff
    autodiff



#exit
#check split_integral_over_set_of_ite


#check SciLean.split_integral_over_set_of_ite


#check ge_iff_le


#check HAdd.hAdd.arg_a0a1.cderiv_rule
