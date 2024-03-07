import SciLean.Modules.Prob.DistribDeriv.DistribDeriv
import SciLean.Modules.Prob.DistribDeriv.DistribFwdDeriv

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace SciLean.Prob

open MeasureTheory

variable
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]


noncomputable
def pureDeriv (x dx : X) : Distribution X := ⟨fun φ => fderiv ℝ φ x dx⟩

noncomputable
def pureFwdDeriv (x dx : X) : FDistribution X := { val := pure x, dval := pureDeriv x dx }


theorem pure_as_dirac (x : X) : (pure x : Distribution X) = (@Measure.dirac _ (borel X) x).toDistribution := by
  ext
  have : @MeasurableSingletonClass X (borel X) := sorry
  simp [pure]
  rw[@MeasureTheory.integral_dirac _ _ _ _ _ (borel X) _]


@[fprop]
theorem pure.differentiableAt (f : X → Y) (φ : Y → W) (x : X)
    (hf : DifferentiableAt ℝ f x) (hφ : DifferentiableAt ℝ φ (f x)) :
    DifferentiableAt ℝ (fun x => ⟪pure (f:=Distribution) (f x), φ⟫) x := by dsimp[pure,action]; fprop

-- this theorem should be unecessary
-- fprop note: `action` should be marked as function coerction then this statement is fvar application case and
-- composition theorem should fire
@[fprop]
theorem action.differentiableAt (g : X → Y) (f : Y → Distribution Z) (φ : Z → W) (x : X)
    (hf : DifferentiableAt ℝ (fun y => ⟪f y, φ⟫) (g x)) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun x => ⟪f (g x), φ⟫) x := sorry

-- @[fprop]
theorem pure.bind._arg_xf.differentiableAt (g : X → Y) (f : X → Y → Distribution Z) (φ : Z → W) (x : X)
    (hg : DifferentiableAt ℝ g x) (hf : DifferentiableAt ℝ (fun (x,y) => ⟪f x y, φ⟫) (x, g x))  :
    DifferentiableAt ℝ (fun x => ⟪(pure (g x)) >>= (f x), φ⟫) x := by

  dsimp only [bind,pure,action]; simp
  -- TODO: fix `fprop` such that it can work with `hf` !!!
  apply DifferentiableAt.comp_rule x (fun x => (x,g x)) (by fprop) _ hf



@[simp]
theorem pure.distribDeriv_comp (f : X → Y) (x dx : X) (φ : Y → W)
    (hg : DifferentiableAt ℝ f x)
    (hφ : DifferentiableAt ℝ φ (f x)) :
    ⟪distribDeriv (fun x : X => pure (f x)) x dx, φ⟫
    =
    let y := f x
    let dy := fderiv ℝ f x dx
    ⟪pureDeriv y dy, φ⟫  := by

  conv =>
    lhs
    unfold distribDeriv; dsimp[pure,action]
    ftrans; dsimp


@[simp]
theorem pure.bind.arg_xf.distribDeriv_rule
    (g : X → Y) (f : X → Y → Distribution Z) (x dx) (φ : Z → W)
    (hg : DifferentiableAt ℝ g x) (hf : DifferentiableAt ℝ (fun (x,y) => ⟪f x y, φ⟫) (x, g x)) :
    ⟪distribDeriv (fun x' => (pure (g x')) >>= (f x')) x dx, φ⟫
    =
    let y := g x
    let dy := fderiv ℝ g x dx
    ⟪(pureDeriv y dy) >>= (f x ·), φ⟫
    +
    ⟪distribDeriv (f · y) x dx, φ⟫ := by

  simp [bind, distribDeriv, pure, pureDeriv,action]
  -- TODO: fix `ftrans` to apply this rule
  have h := fderiv.comp_rule_at ℝ (fun (x,y) => ⟪f x y, φ⟫) (fun x => (x, g x)) x hf (by fprop)
  dsimp at h
  rw[h]; ftrans; dsimp
  rw[fderiv_uncurry (fun x y => ⟪f x y, φ⟫) (x, g x) _ hf]
  simp only [add_comm]


@[simp]
theorem pure.distribFwdDeriv_comp (f : X → Y) (x dx : X) (φ : Y → W×W)
    (hg : DifferentiableAt ℝ f x)
    (hφ : DifferentiableAt ℝ φ (f x)) :
    ⟪distribFwdDeriv (fun x : X => pure (f x)) x dx, φ⟫
    =
    let ydy := fwdFDeriv ℝ f x dx
    ⟪pureFwdDeriv ydy.1 ydy.2, φ⟫ := by

  unfold distribFwdDeriv
  simp (disch:=first | assumption | fprop) [fdaction_mk_apply, distribDeriv_comp, pureFwdDeriv, fwdFDeriv]


@[simp]
theorem pure.bind.arg_xf.distribFwdDeriv_rule
    (g : X → Y) (f : X → Y → Distribution Z) (x dx) (φ : Z → W×W)
    (hg : DifferentiableAt ℝ g x) (hf : DifferentiableAt ℝ (fun (x,y) => ⟪f x y, fun x => (φ x).1⟫) (x, g x)) :
    ⟪distribFwdDeriv (fun x' => bind (pure (g x')) (f x')) x dx, φ⟫
    =
    let ydy := fwdFDeriv ℝ g x dx
    ⟪distribFwdDeriv (fun (x,y) => f x y) (x,ydy.1) (dx,ydy.2), φ⟫ := by

  unfold distribFwdDeriv;
  simp (disch := assumption) only [fdaction_mk_apply, distribDeriv_rule, Prod.mk.injEq]
  -- this should be simplified
  constructor
  . rfl
  . simp (disch := assumption) only [bind, pureDeriv, distribDeriv, pure, fwdFDeriv, add_left_inj,action]
    simp only [distribution_action_normalize]
    rw[fderiv_uncurry (fun x y => ⟪f x y, fun x => (φ x).1⟫) _ _ hf]
    ftrans
    sorry
