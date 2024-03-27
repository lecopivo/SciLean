import SciLean.Core.Distribution.ParametricDistribDeriv
import SciLean.Core.Distribution.SurfaceDirac
import SciLean.Core.Distribution.Eval
import SciLean.Core.Rand.Distributions.UniformI
import SciLean.Core.FunctionTransformations.Preimage
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


def bungeeDomain (height : R) : Set (R×R) := {((x,z) : R×R) | 1 ≤ x ∧ x ≤ height ∧ 0 ≤ z ∧ z ≤ x}

open Rand in
instance (height : R) : Rand.UniformRand (bungeeDomain height) where
  uniform := do
    let x ← uniform (Icc 1 height)
    let z ← uniform (Icc 0 x.1)
    return ⟨(x,z), sorry_proof⟩

@[simp, ftrans_simp]
theorem bungeeDomain_preimage1 (height : R) :
    preimage1 (fun x z => (x, z)) (bungeeDomain height) = Icc 1 height := sorry_proof

@[simp, ftrans_simp]
theorem bungeeDomain_preimage (height : R) (x : R) :
    (fun z => (x, z)) ⁻¹' bungeeDomain height = if x ∈ Icc 1 height then Icc 0 x else ∅ := by
  unfold bungeeDomain; ext; simp[and_assoc]

@[simp, ftrans_simp]
theorem bungeeDomain_volume (height : R) :
    volume (bungeeDomain height) = Scalar.toENNReal (height^2 - 1)/2 := sorry_proof


noncomputable
def velocity (m : R) (l₁ l₂ k₁ k₂ α : R) (bungeeLength : R) : R :=
  (Scalar.sqrt (2 * ∫' z in Ioo 1 bungeeLength, (g - bungeeTension l₁ l₂ k₁ k₂ α z / m)))


noncomputable
def timeToFall (m : R) (l₁ l₂ k₁ k₂ α : R) (height : R) : R :=
  -- ∫' x in Ioo 1 height, 2 * ∫' z in Ioo 0 x, (g - bungeeTension l₁ l₂ k₁ k₂ α z / m)
  ∫' (x,z) in bungeeDomain height, (g - bungeeTension l₁ l₂ k₁ k₂ α z / m)

noncomputable
def timeToFall' (m : R) (l₁ l₂ k₁ k₂ α : R) (height : R) : R :=
  ∫' x in Ioo 1 height, 2 * ∫' z in Ioo 0 x, (g - bungeeTension l₁ l₂ k₁ k₂ α z / m)


noncomputable
def objective (m : R) (l₁ l₂ k₁ k₂ α : R) (height : R) : R :=
  let t := timeToFall m l₁ l₂ k₁ k₂ α height
  let a := g - bungeeTension l₁ l₂ k₁ k₂ α 1 / m
  t + a

def constraint (m : R) (l₁ l₂ k₁ k₂ α : R) (height : R) := velocity m l₁ l₂ k₁ k₂ α 1 = 0

variable (m l₁ l₂ k₁ k₂ α : R) (height : R)

#check (∂ l, velocity m l l₂ k₁ k₂ α height)
  rewrite_by
    unfold velocity bungeeTension
    fun_trans (config:={zeta:=false})

set_option profiler true


attribute [ftrans_simp]
  FiniteDimensional.finrank_self FiniteDimensional.finrank_prod
  not_le ite_mul mul_ite mul_neg mul_one setOf_eq_eq_singleton
  Finset.card_singleton PUnit.default_eq_unit Finset.univ_unique Finset.sum_const
  preimage_id'
  mem_setOf_eq mem_ite_empty_right mem_inter_iff mem_ite_empty_right mem_univ mem_Ioo mem_Icc mem_Ioc mem_Ico mem_compl_iff
  and_true
  bind_assoc pure_bind

attribute [rand_pull_E] bind_assoc pure_bind

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

-- theorem set_inter {α} (P Q : α → Prop) : {x | P x} ∩ {x | Q x} = {x | P x ∧ Q x} := by aesop

-- open Lean Meta in
-- simproc hihi' (Distribution.extAction _ _) := fun e => do

--   -- let φ := e.appArg!
--   -- let T := e.appFn!.appArg!.appArg!.appFn!.appArg!
--   IO.println s!"extAction simproc simplification with distribution {← ppExpr e}"
--   return .continue

-- theorem split_integral {X} {Y} [MeasureSpace X] [MeasureSpace Y] (f : X×Y → R) :
--     ∫' (xy : X×Y), f xy = ∫' x, ∫' y, f (x,y) := sorry_proof

variable (hheight : 1 ≤ height)

-- set_option trace.Meta.Tactic.simp.rewrite true in
#check (∂ l, timeToFall m l l₂ k₁ k₂ α height)
  rewrite_by
    unfold timeToFall bungeeTension scalarCDeriv
    fun_trans (config:={zeta:=false}) only [scalarCDeriv, ftrans_simp, scalarGradient, Tactic.lift_lets_simproc]

    conv =>
      enter[k',k'',l]
      conv in surfaceDirac _ _ _ =>
        rw[surfaceDirac_substitution
            (I:= Unit)
            (X₁:=fun _ => R) (X₂:= fun _ => R)
            (p:= fun _ x y => (x,y))
            (ζ:= fun b _ => l * (k₁ + k₂) / k₂)
            (dom:= fun _ => Set.univ)
            (inv:= by intro i x₁ _; dsimp; sorry_proof) (hdim := sorry_proof)]
        autodiff; autodiff
        fun_trans (config:={zeta:=false}) only [ftrans_simp, scalarGradient, Tactic.lift_lets_simproc]

    simp (config:={zeta:=false}) (disch:=assumption) only [action_push, ftrans_simp]
    fun_trans (config:={zeta:=false}) only [ftrans_simp]
    rand_pull_E
    autodiff

    -- simp (config:={zeta:=false}) only [t3',t4',t1, t2, t4, ftrans_simp,set_inter]

#check Nat

set_option pp.funBinderTypes true in
set_option trace.Meta.Tactic.fun_trans true in
set_option trace.Meta.Tactic.simp.unify true in
set_option trace.Meta.Tactic.simp.discharge true in
#check (cderiv R fun l => timeToFall' m l l₂ k₁ k₂ α height)
  rewrite_by
    unfold timeToFall' bungeeTension
    fun_trans (config:={zeta:=false}) only  -- [ftrans_simp, scalarGradient, Tactic.lift_lets_simproc]

    simp only [ftrans_simp, action_push, Distribution.mk_extAction_simproc]
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
