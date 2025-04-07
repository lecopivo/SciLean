import SciLean.Analysis.ODE.OdeSolve
import SciLean.Analysis.Calculus.Notation.Gradient

import SciLean.Util.SolveFun
import SciLean.Tactic.LetEnter

set_option linter.unusedVariables false

namespace SciLean

variable
  {R : Type _} [RCLike R]
  {W : Type _} [NormedAddCommGroup W] [NormedSpace R W]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace R Z]

set_default_scalar R

def forwardEuler (f : R → X → X) (tₙ Δt : R) (xₙ : X) : X :=
  xₙ + Δt • f tₙ xₙ

noncomputable
def backwardEuler (f : R → X → X) (tₙ Δt : R) (xₙ : X) : X :=
  solve x', x' = xₙ + Δt • f (tₙ + Δt) x'

def explicitMidpoint (f : R → X → X) (tₙ Δt : R) (xₙ : X) : X :=
  let x' := xₙ + (Δt/2) • f tₙ xₙ
  let x'' := xₙ + Δt • f (tₙ+(Δt/2)) x'
  x''

noncomputable
def implicitMidpoint (f : R → X → X) (tₙ Δt : R) (xₙ : X) : X :=
  solve x', x' = xₙ + Δt • f (tₙ+(Δt/2)) ((1/2:R) • (xₙ + x'))

def heunMethod (f : R → X → X) (tₙ Δt : R) (xₙ : X) : X :=
  let x' := xₙ + Δt • f tₙ xₙ
  let x'' := xₙ + (Δt/2) • (f tₙ xₙ + f (tₙ + Δt) x')
  x''

noncomputable
def crankNicolson (f : R → X → X) (tₙ Δt : R) (xₙ : X) : X :=
  solve x', x' = xₙ + (Δt/2) • (f tₙ xₙ + f (tₙ + Δt) x')


def rungeKutta4 (f : R → X → X) (tₙ Δt : R) (xₙ : X) : X :=
  let k₁ := f tₙ xₙ
  let k₂ := f (tₙ + Δt/2) (xₙ + (Δt/2) • k₁)
  let k₃ := f (tₙ + Δt/2) (xₙ + (Δt/2) • k₂)
  let k₄ := f (tₙ + Δt) (xₙ + Δt • k₃)
  xₙ + (Δt/6) • (k₁ + (2:R)•k₂ + (2:R)•k₃ + k₄)


variable
  {X : Type _} [NormedAddCommGroup X] [AdjointSpace R X] [SMul (Rᵐᵒᵖ) X] [Star X]
  {Y : Type _} [NormedAddCommGroup Y] [AdjointSpace R Y]
  {Z : Type _} [NormedAddCommGroup Z] [AdjointSpace R Z]
  {XX : Type _} [NormedAddCommGroup XX] [AdjointSpace R XX]
  [TensorProductType R X X XX] [TensorProductSelf R X XX]


/-- Symplectic Euler integrator

Well behaved integragor for Hamiltonian systems

Warning: This is symplectic integrator if `H q p = T p + V q`.
In more complicated cases use `implicitSymplecticEulerV1` or `implicitSymplecticEulerV2`.
-/
noncomputable
def explicitSymplecticEuler (H : X → X → R) (Δt : R) (qₙ pₙ : X) : X×X :=
  let p' := pₙ - Δt • ∇ (q:=qₙ), H q  pₙ
  let q' := qₙ + Δt • ∇ (p:=p'), H qₙ p
  (q', p')

noncomputable
def implicitSymplecticEulerV1 (H : X → X → R) (Δt : R) (qₙ pₙ : X) : X×X :=
  solve q' p',
    q' = qₙ + Δt • ∇ (p:=p'), H qₙ p
    ∧
    p' = pₙ - Δt • ∇ (q:=qₙ), H q  p'

noncomputable
def implicitSymplecticEulerV2 (H : X → X → R) (Δt : R) (qₙ pₙ : X) : X×X :=
  solve q' p',
    q' = qₙ + Δt • ∇ (p:=pₙ), H q' p
    ∧
    p' = pₙ - Δt • ∇ (q:=q'), H q pₙ

/-- For Hamiltonians in the form `H q p = T p + V q` the `explicitSymplecticEuler` method is identical to `implicitSymplecticEulerV1`
-/
theorem explicitSymplecticEuler_eq_implicitSymplecticEulerV1
  (T V : X → R)
  (hT : Differentiable R T) (hV : Differentiable R V)
  : explicitSymplecticEuler (fun q p => T p + V q)
    =
    implicitSymplecticEulerV1 (fun q p => T p + V q) :=
by
  unfold implicitSymplecticEulerV1
  unfold explicitSymplecticEuler
  conv =>
    rhs
    solve_for p' from 1 := sorry_proof
    solve_as_inv
    solve_as_inv
  conv => lfun_trans
  sorry_proof
