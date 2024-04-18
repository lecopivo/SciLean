import SciLean.Core.Notation
import SciLean.Core.Integral.CIntegral
import SciLean.Core.Integral.ParametricInverse
import SciLean.Core.Integral.Surface

import SciLean.Tactic.RefinedSimp


open MeasureTheory

namespace SciLean


variable
  {R} [RealScalar R]
  {W} [Vec R W]
  {X} [SemiHilbert R X]
  {Y} [Vec R Y] [Module ℝ Y]
  {Z} [Vec R Z] [Module ℝ Z]

set_default_scalar R


def IsLipschitzDomain (A : Set U) : Prop :=
  ∃ (φ : U → ℝ),
    A = {x | φ x = 0}
    -- and some lipshitz contition

-- !!!not sure about the sign!!!
noncomputable
def levelSetSpeed (φ : W → X → R) (w dw : W) (x : X) : R :=
  - (∂ w':=w;dw, (φ w' x)) / ‖∇ (φ w ·) x‖₂

open Classical in
noncomputable
def interfaceSpeed' (A : W → Set X) (w dw : W) (x : frontier (A w)) : R :=
  -- todo: use some version of `IsLipschitzDomain` to get `φ`
  if h : ∃ φ : W → X → R, ∀ w, A w = {x | 0 ≤ φ w x} then
    let φ := choose h
    levelSetSpeed φ w dw x.1
  else
    0

variable (R)
open Classical in
noncomputable
def frontierSpeed (A : W → Set X) (w dw : W) (x : X) : R :=
  -- todo: use some version of `IsLipschitzDomain` to get `φ`
  if h : ∃ φ : W → X → R, ∀ w, A w = {x | 0 ≤ φ w x} then
    let φ := choose h
    -- TODO: turn `x` to the closes point on the boundary
    levelSetSpeed φ w dw x
  else
    0
variable {R}


@[simp, ftrans_simp]
theorem frontierSpeed_levelSet (φ ψ : W → X → R) (w dw : W) (x : X) (h : φ w x = ψ w x) :
     frontierSpeed R (fun w => {x | φ w x ≤ ψ w x}) w dw x
     =
     - (∂ (w':=w;dw), (ψ w' x - φ w' x)) / ‖∇ (x':=x), (ψ w x' - φ w x')‖₂ := sorry_proof


variable [MeasureSpace X]

open FiniteDimensional

-- Probably the domain needs to be differentiable in time and lipschitz in space
@[fun_prop]
theorem moving_volume_differentiable (f : W → X → Y) (A : W → Set X)
    (hf : ∀ x, CDifferentiable R (f · x)) (hA : IsLipschitzDomain {wx : W×X | wx.2 ∈ A wx.1})
    (μ : Measure X) /- todo: add absolute continuous w.r.t to lebesgue measure -/  :
    CDifferentiable R fun  w => ∫' x in A w, f w x ∂μ := sorry_proof

-- Probably the domain needs to be differentiable in time and lipschitz in space
-- @[fun_trans]
theorem moving_volume_derivative (f : W → X → Y) (A : W → Set X) (hA : IsLipschitzDomain {wx : W×X | wx.2 ∈ A wx.1}) :
    (∂ w, ∫' x in A w, f w x)
    =
    fun w dw =>
      (∫' x in A w, (∂ (w':=w;dw), f w' x))
      +
      ∫' x in frontier (A w), (frontierSpeed R A w dw x) • f w x ∂(surfaceMeasure (finrank R X - 1)) := sorry_proof



----------------------------------------------------------------------------------------------------
-- Moving Frontier Integral ------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

variable (R)
noncomputable
def movingFrontierIntegral (A : W → Set X) (B : Set X) (f : X → Y) (w dw : W) : Y :=
  ∫' x in frontier (A w) ∩ B, frontierSpeed R A w dw x • f x
variable {R}


@[rsimp ↓]
noncomputable
def movingFrontierIntegral_inter (A A' : W → Set X) (B : Set X) (f : X → Y)
    (hA : ∀ w, surfaceMeasure (finrank R X - 1) (frontier (A w) ∩ frontier (A' w)) = 0) :
    movingFrontierIntegral R (fun w => A w ∩ A' w) B f
    =
    fun w dw =>
      movingFrontierIntegral R (fun w => A w) (B ∩ A' w) f w dw
      +
      movingFrontierIntegral R (fun w => A' w) (B ∩ A w) f w dw := sorry_proof


@[rsimp ↓]
noncomputable
def movingFrontierIntegral_union (A A' : W → Set X) (B : Set X) (f : X → Y)
    (hA : ∀ w, surfaceMeasure (finrank R X - 1) (frontier (A w) ∩ frontier (A' w)) = 0) :
    movingFrontierIntegral R (fun w => A w ∪ A' w) B f
    =
    fun w dw =>
      movingFrontierIntegral R (fun w => A w) (B ∩ (A' w)ᶜ) f w dw
      +
      movingFrontierIntegral R (fun w => A' w) (B ∩ (A w)ᶜ) f w dw := sorry_proof


-- We need a specialized simproc for this as lhs matches on rhs. This leads to infinite recursion
@[rsimp ↓ guard A .notConst]
theorem cintegral.arg_fμ.cderiv_rule (f : W → X → Y) (A : W → Set X)
    (hA : IsLipschitzDomain {wx : W×X | wx.2 ∈ A wx.1}) :
    (∂ w, ∫' x in A w, f w x)
    =
    fun w dw =>
      let ds := movingFrontierIntegral R A ⊤ (f w) w dw
      let di := ∂ (w':=w;dw), ∫' x in A w, f w' x
      ds + di := sorry_proof


@[rsimp ↓ guard A .notConst]
theorem cintegral.arg_fμ.fwdDeriv_rule (f : W → X → Y) (A : W → Set X)
    (hA : IsLipschitzDomain {wx : W×X | wx.2 ∈ A wx.1}) :
    (∂ w, ∫' x in A w, f w x)
    =
    fun w dw =>
      let ds := movingFrontierIntegral R A ⊤ (f w) w dw
      let di := ∂ (w':=w;dw), ∫' x in A w, f w' x
      ds + di := sorry_proof


@[rsimp ↓]
theorem cintegral.arg_fμ.cderiv_rule_if_le (f g : W → X → Y) (φ ψ : W → X → R) (A : Set X) :
    (∂ w, ∫' x in A, if φ w x ≤ ψ w x then f w x else g w x)
    =
    fun w dw =>
      let ds := movingFrontierIntegral R (fun w => {x : X | φ w x ≤ ψ w x}) ⊤ (fun x => f w x - g w x) w dw
      let dy := ∂ (w':=w;dw), ∫' x in (A ∩ {x : X | φ w x ≤ ψ w x}), f w' x
      let dz := ∂ (w':=w;dw), ∫' x in (A ∩ {x : X | ψ w x < φ w x}), g w' x
      ds + dy + dz := sorry_proof


@[rsimp ↓]
theorem cintegral.arg_fμ.cderiv_rule_if_lt (f g : W → X → Y) (φ ψ : W → X → R) (A : Set X) :
    (∂ w, ∫' x in A, if φ w x < ψ w x then f w x else g w x)
    =
    fun w dw =>
      let ds := movingFrontierIntegral R (fun w => {x : X | φ w x < ψ w x}) ⊤ (fun x => f w x - g w x) w dw
      let dy := ∂ (w':=w;dw), ∫' x in (A ∩ {x : X | φ w x < ψ w x}), f w' x
      let dz := ∂ (w':=w;dw), ∫' x in (A ∩ {x : X | ψ w x ≤ φ w x}), g w' x
      ds + dy + dz := sorry_proof
