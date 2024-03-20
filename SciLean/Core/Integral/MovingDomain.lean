import SciLean.Core.Notation
import SciLean.Core.Integral.CIntegral
import SciLean.Core.Integral.ParametricInverse
import SciLean.Core.Integral.Surface

open MeasureTheory

namespace SciLean


variable
  {R} [RealScalar R]
  {W} [SemiHilbert R W]
  {X} [SemiHilbert R X]
  {Y} [SemiHilbert R Y] [Module ℝ Y]
  {Z} [SemiHilbert R Z] [Module ℝ Z]

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
theorem moving_volume_differentiable (f : W → X → Y) (A : W → Set X) (hA : IsLipschitzDomain {wx : W×X | wx.2 ∈ A wx.1}) :
    CDifferentiable R fun  w => ∫' x in A w, f w x := sorry_proof


-- Probably the domain needs to be differentiable in time and lipschitz in space
@[fun_trans]
theorem moving_volume_derivative (f : W → X → Y) (A : W → Set X) (hA : IsLipschitzDomain {wx : W×X | wx.2 ∈ A wx.1}) :
    (∂ w, ∫' x in A w, f w x)
    =
    fun w dw =>
      (∫' x in A w, (∂ (w':=w;dw), f w' x))
      +
      ∫' x in frontier (A w), (frontierSpeed R A w dw x) • f w x ∂(surfaceMeasure (finrank R X - 1)) := sorry_proof
