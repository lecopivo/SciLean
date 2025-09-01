import Mathlib.MeasureTheory.Measure.VectorMeasure
import Mathlib.Logic.Function.Basic

import SciLean.Modules.Prob.DRand

open MeasureTheory ENNReal BigOperators Finset

namespace SciLean.Prob

structure FDRand (X : Type) [MeasurableSpace X] where
  val  : Rand X
  dval : DRand X

noncomputable
def randFwdDeriv {X} [NormedAddCommGroup X] [NormedSpace ℝ X] {Y} [MeasurableSpace Y]
    (f : X → Rand Y) (x dx : X) : FDRand Y := ⟨f x, randDeriv f x dx⟩

instance {X} [MeasurableSpace X] : MeasurableSpace (FDRand X) := sorry

open Rand

variable
  {R} [RealScalar R]
  {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace R X] [MeasurableSpace X]
  {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedSpace R Y] [MeasurableSpace Y]
  {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedSpace R Z] [MeasurableSpace Z]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace R W] [MeasurableSpace W]


namespace FDRand

@[ext]
theorem ext (x y : FDRand X) : x.val = y.val → x.dval = x.dval → x = y := sorry


----------------------------------------------------------------------------------------------------
-- Monadic operations ------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

noncomputable
def fdpure (x dx : X) : FDRand X := {
  val  := pure x
  dval := dpure x dx
 }

noncomputable
def bind (x : FDRand X) (f : X → FDRand Y) : FDRand Y := {
  val  := x.val.bind (fun x' => (f x').val)
  dval := x.dval.bindDR (fun x' => (f x').val) +
          x.val.bindRD (fun x' => (f x').dval)
}

noncomputable
def join (x : FDRand (FDRand X)) : FDRand X := x.bind id


@[rand_simp,simp]
theorem bind_bind (x : FDRand X) (g : X → FDRand Y) (f : Y → FDRand Z) :
    bind (bind x g) f = bind x fun x' => bind (g x') f := by

  apply ext
  . simp (disch:=sorry) only [bind,rand_simp]
  . simp (disch:=sorry) only [bind,rand_simp]


-- @[rand_simp,simp]
theorem bind_pure (f : X → FDRand Y) (x dx : X) :
    (fdpure x dx).bind f
    =
    ⟨(f x).val, randDeriv (fun x' => (f x').val) x dx + (f x).dval⟩ := by

  simp only [bind,fdpure]
  apply ext
  . simp (disch:=sorry) only [rand_simp]
  . simp only [rand_simp]


@[rand_simp,simp]
theorem bind_pure_zero (f : X → FDRand Y) (x : X) :
    (fdpure x 0).bind f = f x := by

  simp only [bind,fdpure]
  apply ext
  . simp (disch:=sorry) only [rand_simp]
  . simp only [rand_simp]



----------------------------------------------------------------------------------------------------
-- Notation ----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- we can't use do notation because Rand is not a monad right now (because of the [MeasurableSpace X] argument)
-- this is a small hack to recover it a bit
open Lean.Parser Term in
syntax withPosition("let" funBinder " ~~ " term semicolonOrLinebreak ppDedent(ppLine) term) : term
macro_rules
  | `(let $x ~~ $y; $b) => do Pure.pure (← `(Probly.FDRand.bind $y (fun $x => $b))).raw


open Lean Parser
@[app_unexpander FDRand.bind] def unexpandFDRandBind : Lean.PrettyPrinter.Unexpander

| `($(_) $y $f) =>
  match f.raw with
  | `(fun $x:term => $b) => do
    let s ←
      `(let $x ~~ $y
        $b)
    Pure.pure s.raw
  | _ => throw ()

| _ => throw ()



----------------------------------------------------------------------------------------------------
-- Expected Value and Change -----------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

noncomputable
def fdE (x : FDRand X) (φ : X → Y) : Y×Y := (x.val.E φ, x.dval.dE φ)

noncomputable
def fdE' (x : FDRand X) (φ : X → Y×Y) : Y×Y := (x.val.E (fun x => (φ x).1), x.dval.dE (fun x => (φ x).1) + x.val.E (fun x => (φ x).2))

@[simp,rand_push_E]
theorem fdpure_fdE (x dx : X) (φ : X → Y) :
    (fdpure x dx).fdE φ = (φ x, fderiv ℝ φ x dx) := by

  simp (disch:=sorry) only [fdpure,fdE,rand_simp]

@[simp,rand_push_E]
theorem bind_fdE (x : FDRand X) (f : X → FDRand Y) (φ : Y → Z) :
    ((x.bind f).fdE φ)
    =
    (x.fdE' (fun x' => (f x').fdE φ)) := by

  simp (disch:=sorry) only [bind,fdpure,fdE,fdE',rand_simp,rand_push_E]

@[simp,rand_push_E]
theorem bind_fdE' (x : FDRand X) (f : X → FDRand Y) (φ : Y → Z×Z) :
    ((x.bind f).fdE' φ)
    =
    (x.fdE' (fun x' => (f x').fdE' φ)) := by

  simp (disch:=sorry) only [bind,fdpure,fdE,fdE',rand_simp,rand_push_E,add_assoc]


@[simp,rand_push_E]
theorem FDRand_mk_zero_fdE (x : Rand X) (φ : X → X) :
    (FDRand.mk x 0).fdE φ = (x.E φ, (0 : X)) := by
  simp [fdE,DRand.dE]
  apply testFunctionExtension_ext
  intro _ _
  simp [rand_simp,zero_smul]

theorem FDRand_mk_fdE (x : Rand X) (dx : DRand X) (φ : X → Y) :
    (FDRand.mk x dx).fdE φ = (x.E φ, dx.dE φ) := by rfl

def _root_.SciLean.Prob.weightByDensity (p q : R) (y : Y) : Y×Y := (p • y, q • y)
def _root_.SciLean.Prob.weightByDensity' (p q : R) (ydy : Y×Y) : Y×Y := (p • ydy.1, q • ydy.1 + p • ydy.2)
def _root_.SciLean.Prob.weightByDensityM' (p q : R) (ydy : Rand (Y×Y)) : Rand (Y×Y) := let ydy' ~ ydy; pure (weightByDensity' p q ydy')

variable (R)
theorem fdE_as_E {rx : FDRand X} {φ : X → Y} (rx' : Rand X) :
  rx.fdE φ = rx'.E (fun x => weightByDensity (rx.val.pdf R rx'.μ x) (rx.dval.density R rx'.μ x) (φ x)) := sorry

theorem fdE'_as_E {rx : FDRand X} {φ : X → Y×Y} (rx' : Rand X) :
  rx.fdE' φ = rx'.E (fun x => weightByDensity' (rx.val.pdf R rx'.μ x) (rx.dval.density R rx'.μ x) (φ x)) := sorry

theorem fdE'_as_E_simple {r : Rand X} {φ : X → Y×Y}  :
  (FDRand.mk r 0).fdE' φ = r.E φ := sorry

variable {R}

noncomputable
def fdmean (x : FDRand X) : X×X := x.fdE id

@[rand_pull_E]
theorem expectedValueAndChange_as_fdmean (x : FDRand X) (φ : X → Y) :
    x.fdE φ = (x.bind (fun x' => fdpure (φ x') 0)).fdmean := by

  simp (disch:=sorry) only [rand_simp,mean,fdE,fdmean,bind,fdpure,id]
  simp
