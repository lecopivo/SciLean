import SciLean.Core.Rand.Rand
import SciLean.Core.Rand.Distributions.Normal
import SciLean.Core.Distribution.Basic
import SciLean.Core.Distribution.ParametricDistribDeriv

import SciLean.Tactic.IfPull

import Mathlib.MeasureTheory.Constructions.Prod.Basic
namespace SciLean.Rand

variable {R} [RealScalar R]

section MeasureCondition

open MeasureTheory

variable [MeasurableSpace X] [MeasurableSpace Y]

open Classical in
noncomputable
def _root_.MeasureTheory.Measure.condition
    [MeasurableSpace X] [MeasurableSpace X₁] [MeasurableSpace X₂]
    (μ : Measure X) (mk : X₁ → X₂ → X) (x₁ : X₁) : Measure X₂ :=
  if h : ∃ μ₂ : X₁ → Measure X₂, ∀ (μ₁ : Measure X₁), (μ₁.bind (fun x₁ => (μ₂ x₁).bind (fun x₂ => Measure.dirac (mk x₁ x₂)))) = μ then
    choose h x₁
  else
    default

noncomputable
abbrev _root_.MeasureTheory.Measure.conditionFst
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure (X×Y)) (x : X) : Measure Y := μ.condition (fun x y => (x,y)) x

noncomputable
abbrev _root_.MeasureTheory.Measure.conditionSnd
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure (X×Y)) (y : Y) : Measure X := μ.condition (fun y x => (x,y)) y

@[simp, ftrans_simp]
theorem Measure.condition_fst_prod (μ : Measure X) (ν : Measure Y) :
    (μ.prod ν).map Prod.fst
    =
    μ := sorry_proof

attribute [simp, ftrans_simp] MeasureTheory.Measure.fst_prod MeasureTheory.Measure.snd_prod

-- @[simp, ftrans_simp]
-- theorem _root_.Measure.map_fst_volume {X Y} [MeasureSpace X] [MeasureSpace Y] :
--     (volume : Measure (X×Y)).fst
--     =
--     volume := by
--   simp [volume,Measure.snd]
--   apply MeasureTheory.Measure.fst_prod



-- @[simp, ftrans_simp]
-- theorem Measure.map_snd_volume {X Y} [MeasureSpace X] [MeasureSpace Y] :
--     (volume : Measure (X×Y)).snd Prod.snd
--     =
--     volume := by simp [volume]

end MeasureCondition



open Classical in
/-- If `X` decomposes into `X₁` and `X₂` then we can condition `rx : Rand X` with `x₁ : X₁`
and obtain random variable on `X₂`. -/
noncomputable
def condition [Inhabited X₂] (rx : Rand X) (mk : X₁ → X₂ → X) (x₁ : X₁) : Rand X₂ :=
  if h : ∃ rx₂ : X₁ → Rand X₂, ∀ (rx₁ : Rand X₁), (do let x₁ ← rx₁; let x₂ ← rx₂ x₁; return mk x₁ x₂) = rx then
    choose h x₁
  else
    return default

/-- Condition on the first variable of a pair. -/
noncomputable
abbrev conditionFst [Inhabited X₂] (rx : Rand (X₁×X₂))  (x₁ : X₁) : Rand X₂ := rx.condition Prod.mk x₁

/-- Condition on the second variable of a pair. -/
noncomputable
abbrev conditionSnd [Inhabited X₁] (rx : Rand (X₁×X₂))  (x₂ : X₂) : Rand X₁ := rx.condition (fun x₂ x₁ => (x₁,x₂)) x₂

@[simp, ftrans_simp]
theorem Rand.bind_bind_condition [Inhabited X₂] (rx : Rand X) (mk : X₁ → X₂ → X) (prior : Rand X₁) (f : X → α) :
    (do
      let x₁ ← prior
      let x₂ ← rx.condition mk x₁
      return f (mk x₁ x₂))
    =
    do return (f (← rx)) := sorry_proof


----------------------------------------------------------------------------------------------------
-- Model Bind --------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

/-- Special form of bind for `Rand` for which it is easy to compute conditional probabilities and
probability densities. Most likely you want to use this bind when defining probabilistic model. -/
def modelBind (x : Rand X) (f : X → Rand Y) : Rand (X×Y) := do
  let x' ← x
  let y' ← f x'
  return (x',y')

----------------------------------------------------------------------------------------------------
-- Notation ----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- we can't use do notation because Rand is not a monad right now (because of the [MeasurableSpace X] argument)
-- this is a small hack to recover it a bit
open Lean.Parser Term in
syntax withPosition("let" funBinder " ~ " term (semicolonOrLinebreak ppDedent(ppLine) term)?) : term
macro_rules
  | `(let $x ~ $y; $b) => do Pure.pure (← `(SciLean.Rand.modelBind $y (fun $x => $b))).raw
  | `(let $_ ~ $y) => `($y)

open Lean Parser
@[app_unexpander SciLean.Rand.modelBind] def unexpandRandBind : Lean.PrettyPrinter.Unexpander

| `($(_) $y $f) =>
  match f.raw with
  | `(fun $x:term => $b) => do
    let s ←
      `(let $x ~ $y
        $b)
    Pure.pure s.raw
  | _ => throw ()

| _ => throw ()


----------------------------------------------------------------------------------------------------

@[ftrans_simp]
theorem modelBind_condition [Inhabited Y] (x : Rand X) (f : X → Rand Y) (x' : X) :
  (x.modelBind f).condition (fun x y => (x,y)) x'
  =
  f x' := sorry_proof


open MeasureTheory
variable [MeasureSpace X] [MeasureSpace Y]
@[ftrans_simp]
theorem modelBind_pdf (x : Rand X) (f : X → Rand Y) :
  (x.modelBind f).pdf R (volume : Measure (X×Y))
  =
  fun xy => (x.pdf R volume xy.1) * (f xy.1).pdf R volume xy.2 := sorry_proof


-- @[ftrans_simp]
-- theorem if_contidion [Inhabited X₂] {c} [Decidable c] (t e : Rand X) (mk : X₁ → X₂ → X) (x₁ : X₁) :
--   (if c then t else e).condition mk x₁
--   =
--   if c then t.condition mk x₁ else e.condition mk x₁ := sorry_proof



----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

variable [Inhabited X]
noncomputable
def posterior (prior : Rand X) (likelihood : X → Rand Y) (obs : Y) : Rand X := do
  let joint := do
    let x ← prior
    let y ← likelihood x
    return (x,y)

  joint.condition (fun y x => (x,y)) obs

open MeasureTheory
variable {X Z} [MeasurableSpace X] [MeasurableSpace Z] [Inhabited Z]

/-- Kullback–Leibler divergence of `Dₖₗ(P‖Q)` -/
noncomputable
def KLDiv (P Q : Rand X) : R := P.𝔼 (fun x => Scalar.log (P.pdf R Q.ℙ x))


noncomputable
def ELBO {X Z} [MeasureSpace Z] [MeasureSpace X]
  (P : Rand (Z×X)) (Q : Rand Z) (x : X) : R := - Q.𝔼 (fun z => Scalar.log (Q.pdf R volume z) - Scalar.log (P.pdf R volume (z,x)))

noncomputable
def kldiv_elbo
    {X Z} [MeasureSpace Z] [MeasureSpace X] [Inhabited Z]
    (P : Rand (Z×X)) (Q : Rand Z) (x : X) :
    KLDiv (R:=R) Q (P.conditionSnd x)
    =
    let a := (Scalar.log (P.snd.pdf R volume x))
    let b := ELBO P Q x
    a - b := sorry_proof


variable
  {W} [Vec R W]
  [Vec R X]

@[fun_trans]
theorem KLDiv.arg_P.cderiv_rule (P : W → Rand X) (Q : Rand X) :
    cderiv R (fun w => KLDiv (R:=R) (P w) Q)
    =
    fun w dw =>
      let dP := parDistribDeriv (fun w => (P w).ℙ.toDistribution (R:=R)) w dw
      dP.extAction' (fun x => Scalar.log ((P w).pdf R Q.ℙ x) - 1) := sorry_proof

-----------------------------------------------------------------------------------------------

variable [MeasureSpace R]

def model : Rand (R×R) :=
  let v ~ normal 0 5
  if v > 0 then
    let obs ~ normal 1 1
  else
    let obs ~ normal (-2) 1

def prior : Rand R := normal 0 5

def likelihood (v : R) : Rand R := model.conditionFst v
  rewrite_by
    unfold model
    simp only [ftrans_simp]

def guide (θ : R) : Rand R := normal θ 1

variable [MeasureSpace R]

#check ((model (R:=R)).pdf R volume) rewrite_by
  unfold model
  simp only [ftrans_simp]

noncomputable
def loss (θ : R) := KLDiv (R:=R) (guide θ) (model.conditionSnd 0)

set_default_scalar R

-- #check map

variable [AddCommGroup Z] [Module ℝ Z]

#check Rand.pdf

theorem log_mul (x y : R) : Scalar.log (x*y) = Scalar.log x + Scalar.log y := sorry_proof
theorem log_one : Scalar.log (1:R) = 0 := sorry_proof
theorem log_div (x y : R) : Scalar.log (x/y) = Scalar.log x - Scalar.log y := sorry_proof
theorem log_exp (x : R) : Scalar.log (Scalar.exp x) = x := sorry_proof


-- theorem reparameterize (f : X → Y) {r : Rand X} {φ : X → Z} :
--     r.E φ = (r.map f).E (fun y => φ (f.invFun y)) := sorry_proof

open Scalar RealScalar
set_option trace.Meta.Tactic.fun_trans true in
set_option trace.Meta.Tactic.if_pull true in
set_option profiler true in
#check (∂ θ : R, loss θ) rewrite_by
  unfold loss
  simp only [kldiv_elbo]
  unfold ELBO
  unfold guide
  -- tactic =>
  --   let h := reparameterize (fun x : R => x - θ) (hf := sorry)
  conv in Rand.𝔼 _ _ =>
    rw[reparameterize (fun x : R => x - θ) sorry_proof]
    lautodiff -- fun_trans only [ftrans_simp]
    unfold model
    lsimp (config:={zeta:=false}) only
      [ftrans_simp,log_mul,log_div,log_one,log_exp,Tactic.lift_lets_simproc,Tactic.if_pull]

    -- lsimp (config:={zeta:=false}) only [log_mul,log_div,log_exp,log_one,gaussian,Tactic.lift_lets_simproc,ftrans_simp, ← add_sub]
    -- simp (config:={zeta:=false}) only [Tactic.if_pull]

  unfold scalarCDeriv
  lautodiff

  -- unfold model
  -- unfold scalarCDeriv
  -- fun_trans
  -- fun_trans
