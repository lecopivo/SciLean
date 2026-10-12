module

public import SciLean.Analysis.ODE.OdeSolve
public import SciLean.Analysis.Calculus.Notation.Gradient

public import SciLean.Util.SolveFun
public import SciLean.Tactic.LetEnter

@[expose] public section


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
  have shift : ∀ (g : X → R) (c : R) g', HasVecFwdFDeriv R X g g' →
      HasVecFwdFDeriv R X (fun y => g y + c) (fun x dx => ((g' x dx).1 + c, (g' x dx).2)) := by
    intro g c g' hg
    obtain ⟨df, hdf, ht⟩ := hg.deriv
    exact ⟨fun x dx => by rw [hg.val], ⟨df, fun x => (hdf x).add_const c, ht⟩, hg.linear⟩
  have hJ : ∀ (g : X → R) (c : R) x, jacobianMat R (fun y => g y + c) x = jacobianMat R g x := by
    intro g c x
    unfold jacobianMat
    by_cases hg : ∃ g', HasVecFwdFDeriv R X g g'
    · obtain ⟨g', hg'⟩ := hg
      rw [vecFwdFDeriv_from_hasVecFwdFDeriv (shift g c g' hg'),
        vecFwdFDeriv_from_hasVecFwdFDeriv hg']
    · have hn : ¬∃ g', HasVecFwdFDeriv R X (fun y => g y + c) g' :=
        fun ⟨g', hg'⟩ => hg ⟨_, by simpa using shift _ (-c) _ hg'⟩
      simp [vecFwdFDeriv, hg, hn]
  have hJ' : ∀ (g : X → R) (c : R) x, jacobianMat R (fun y => c + g y) x = jacobianMat R g x := by
    intro g c x; simp_rw [add_comm c]; exact hJ g c x
  funext Δt qₙ pₙ
  unfold explicitSymplecticEuler implicitSymplecticEulerV1
  simp only [hJ, hJ']
  have hu : HasUniqueSolution (fun q' p' : X =>
      q' = qₙ + Δt • jacobianMat R T p' ∧ p' = pₙ - Δt • jacobianMat R V qₙ) := by
    refine ⟨⟨⟨(qₙ + Δt • jacobianMat R T (pₙ - Δt • jacobianMat R V qₙ),
      pₙ - Δt • jacobianMat R V qₙ), rfl, rfl⟩⟩, ?_⟩
    rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨h1, h2⟩ ⟨h1', h2'⟩
    subst h2 h2' h1 h1'
    rfl
  simp only [solveFun, hu, ↓reduceDIte]
  obtain ⟨h1, h2⟩ := Classical.choose_spec hu.ex
  exact hu.uniq _ _ ⟨rfl, rfl⟩ ⟨h1, h2⟩
