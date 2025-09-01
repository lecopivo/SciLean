import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Analysis.SpecialFunctions.Inner
import SciLean.Analysis.SpecialFunctions.Norm2
import SciLean.Analysis.AdjointSpace.Geometry

import SciLean.Tactic.Autodiff
-- import SciLean.Tactic.GTrans

set_option linter.unusedVariables false
set_option deprecated.oldSectionVars true

open MeasureTheory Topology Filter FiniteDimensional

namespace SciLean

variable
  {R} [RealScalar R] [MeasureSpace R]
  {W} [NormedAddCommGroup W] [NormedSpace R W]
  {U} [NormedAddCommGroup U] [NormedSpace R U]
  {X} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X] --[NormedSpace ℝ X] [CompleteSpace X] [MeasureSpace X]
  {Y} [NormedAddCommGroup Y] [AdjointSpace R Y] [CompleteSpace Y] --[NormedSpace ℝ Y] [CompleteSpace Y] [MeasureSpace X]
  -- {Y} [NormedAddCommGroup Y] [NormedSpace R Y] [NormedSpace ℝ Y]
  -- {Y₁} [NormedAddCommGroup Y₁] [NormedSpace R Y₁] [NormedSpace ℝ Y₁]
  -- {Y₂} [NormedAddCommGroup Y₂] [NormedSpace R Y₂] [NormedSpace ℝ Y₂]
  -- {Z} [NormedAddCommGroup Z] [NormedSpace R Z] [NormedSpace ℝ Z]

set_default_scalar R


variable (R)
open Classical in
/-- Speed of the frontier of `A (w + t•dw)` in to normal direction at point `x` and time `t=0`. -/
@[fun_trans]
noncomputable
def frontierSpeed (A : W → Set X) (w dw : W) (x : X) : R :=
  match Classical.dec (∃ (φ : W → X → R), (∀ w, closure (A w) = {x | φ w x ≤ 0})) with
  | .isTrue h =>
    let φ := Classical.choose h
    (-(fderiv R (φ · x) w dw)/‖fgradient (φ w ·) x‖₂)
  | .isFalse _ => 0


-- WARNING: All the following rules are correct only on the frontier of the set
--          For now we do not add this requirement as we don't have a good automation to prove it
--          or to assume it and warn user about it.


@[fun_trans]
theorem frontierSpeed.const_rule (A : Set X) /- (hx : x ∈ frontier A) -/ :
  frontierSpeed R (fun w : W => A)
  =
  fun w dw x => 0 := sorry_proof


@[fun_trans]
theorem frontierSpeed.comp_rule
    (f : U → Set X) (g : W → U) (hg : Differentiable R g) /- (hx : x ∈ frontier (f (g w))) -/ :
    frontierSpeed R (fun w => f (g w))
    =
    fun w dw x =>
      let udu := fwdFDeriv R g w dw
      frontierSpeed R f udu.1 udu.2 x := sorry_proof


----------------------------------------------------------------------------------------------------
open Classical Metric in
noncomputable
def _root_.Set.sdf (A : Set X) (x : X) : R :=
  let A := closure A
  if x ∈ A then
    Scalar.ofReal R (- infDist x Aᶜ)
  else
    Scalar.ofReal R (infDist x A)


-- todo: the value is not good in case `d₁ > 0` and `d₂ > 0` then we should do some more elaborate
--       mix of the values
@[fun_trans]
theorem _root_.Set.prod.arg_st.frontierSpeed_rule (s : W → Set X) (t : W → Set Y) :
    frontierSpeed R (fun w => s w ×ˢ t w)
    =
    fun w dw x =>
      let ds := frontierSpeed R s w dw x.1
      let dt := frontierSpeed R t w dw x.2
      let d₁ := Set.sdf R (s w) x.1
      let d₂ := Set.sdf R (t w) x.2
      if d₁ < d₂ then
        dt
      else
        ds := by
  sorry_proof

----------------------------------------------------------------------------------------------------


@[simp, simp_core]
theorem _root_.setOf.arg_p.frontierSpeed_rule_le (φ ψ : W → X → R) :
    frontierSpeed R (fun w => {x | φ w x ≤ ψ w x})
    =
    fun w dw x =>
      let ζ := (fun w x => φ w x - ψ w x)
      (-(fderiv R (ζ · x) w dw)/‖fgradient (ζ w ·) x‖₂) := by
  sorry_proof


@[simp, simp_core]
theorem _root_.setOf.arg_p.frontierSpeed_rule_lt (φ ψ : W → X → R) :
    frontierSpeed R  (fun w => {x | φ w x < ψ w x})
    =
    fun w dw x =>
      let ζ := (fun w x => φ w x - ψ w x)
      (-(fderiv R (ζ · x) w dw)/‖fgradient (ζ w ·) x‖₂) := by
  sorry_proof


----------------------------------------------------------------------------------------------------
-- Intervals ---------------------------------------------------------------------------------------

@[fun_trans]
theorem _root_.Set.Icc.arg_ab.frontierSpeed_rule /- (hx : frontier (Icc a b)) (hab : hab.1 ≠ hab.2) -/ :
    frontierSpeed R (fun ((a,b) : R×R) => Set.Icc a b)
    =
    fun ab dab x =>
      if ab.2 ≤ ab.1 then
        0
      else
        let m := (ab.1 + ab.2)/2
        if x < m then
          - dab.1
        else
          dab.2 := by
  sorry_proof



----------------------------------------------------------------------------------------------------
-- Balls -------------------------------------------------------------------------------------------

@[fun_trans]
theorem closedBall₂.arg_xr.frontierSpeed_rule :
    frontierSpeed R (fun ((c,r) : X×R) => closedBall₂ c r)
    =
    fun cr dcr =>
      let dz := 2 * dcr.2 * cr.2;
      fun x =>
        let y := x - cr.1;
        let dz_1 := - 2 * ⟪dcr.1, y⟫[R];
        let dy := (2:R) • y;
        (dz - dz_1) / ‖dy‖₂[R] := by

  unfold closedBall₂
  funext w dw x
  conv => fun_trans [fgradient]
  set_option trace.Meta.Tactic.fun_trans true in
  conv => fun_trans
  simp[smul_sub]

@[fun_trans]
theorem ball₂.arg_xr.frontierSpeed_rule :
    frontierSpeed R (fun ((c,r) : X×R) => ball₂ c r)
    =
    fun cr dcr =>
      let dz := 2 * dcr.2 * cr.2;
      fun x =>
        let y := x - cr.1;
        let dz_1 := - 2 * ⟪dcr.1, y⟫[R];
        let dy := (2:R) • y;
        (dz - dz_1) / ‖dy‖₂[R] := by

  unfold ball₂
  funext w dw x
  conv => fun_trans [fgradient]
  simp[smul_sub]



-- theorem _root_.Set.Icc.arg_ab.frontierSpeed_rule /- (hx : frontier (Icc a b)) (hab : hab.1 ≠ hab.2) -/ :
--     frontierSpeed R (fun ((a,b) : R×R) => Set.Icc a b)


-- #check setOf

-- fun_trans does not work on this one

@[fun_trans]
example (φ ψ : W → X → R) :
    frontierSpeed R  (fun w => {x | φ w x ≤ ψ w x})
    =
    fun w dw x =>
      let ζ := (fun w x => φ w x - ψ w x)
      (-(fderiv R (ζ · x) w dw)/‖fgradient (ζ w ·) x‖₂) := by
  fun_trans




set_option linter.unusedVariables false in
open Set in
@[simp,simp_core]
theorem frontierSpeed_Icc (a b : W → R) (ha : Differentiable R a) (hb : Differentiable R b) :
    frontierSpeed R  (fun w => Icc (a w) (b w))
    =
    fun w dw x =>
      let ada := fwdFDeriv R a w dw
      let bdb := fwdFDeriv R b w dw
      if bdb.1 ≤ ada.1 then
        0
      else
        let m := (ada.1 + bdb.1)/2
        if x < m then
          - ada.2
        else
          bdb.2 := by
  fun_trans
