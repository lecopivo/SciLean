import SciLean.Core
-- import SciLean.Functions.Limit
-- import SciLean.Functions.OdeSolve


namespace SciLean

#exit

/-- Solution of differential-algebraic equation in fully implicit form:
`
  ∀ t, 0 = f t (ⅆ x t) (x t)
`

-/
noncomputable
def odeSolveFullyImplicit {X Y} [Vec X] [Vec Y] (f : ℝ → X → X → Y) (t : ℝ) (x₀ v₀ : X) : X :=
  let solution_exists := ∃ (x : ℝ → X) (_ : IsSmooth x),
      ∀ t, 0 = f t (ⅆ x t) (x t)
      ∧
      x 0 = x₀ ∧ ⅆ x 0 = v₀
  match Classical.dec solution_exists with
  | isFalse _ => 0
  | isTrue h =>
    let x := Classical.choose h
    x t


noncomputable
def odeSolveSemiImplicit {X Y} [Vec X] [Vec Y]
  (f : ℝ → X → Y → X) (g : ℝ → X → Y → Y)
  (t : ℝ) (x₀ : X) (y₀ : Y)
  : X × Y :=
  let solution_exists := ∃ (x : ℝ → X) (y : ℝ → Y) (_ : IsSmooth x) (_ : IsSmooth y),
      ∀ t, (ⅆ x t = f t (x t) (y t) ∧
            0 = g t (x t) (y t))
      ∧
      x 0 = x₀ ∧ y 0 = y₀
  match Classical.dec solution_exists with
  | isFalse _ => 0
  | isTrue h =>
    let x := Classical.choose h
    let y := Classical.choose (Classical.choose_spec h)
    (x t, y t)


/--
  Semi-implicit ODE can be rewriten as a normal ODE if the constrain has invertible jacobian in `y`
-/
theorem odeSolveSemiImplicit_as_odeSolve {X Y} [Vec X] [Vec Y]
  (f : ℝ → X → Y → X) (g : ℝ → X → Y → Y)
  (t : ℝ) (x₀ : X) (y₀ : Y)
  (valid_constraint : ∀ t x y, IsInv (∂ (g t x) y))
  :
  odeSolveSemiImplicit f g t x₀ y₀
  =
  let g' t x y :=
    (∂ (g t x) y)⁻¹ (∂ (g t) x (f t x y) y)
  odeSolve (λ t xy => (f t xy.1 xy.2, g' t xy.1 xy.2)) t (x₀,y₀)
  :=
  sorry_proof


/--
  The idea for this spliting is that we can approximate `y t ≈ y₀ + t * Δy`
  Then the evolution of `x` looks like:

    `ⅆ x t = f t (x t) (y₀ + t * Δy)`

  First order Taylor expansion yieds

    `ⅆ x t = f t (x t) y₀ + ∂ (f t (x t)) y₀ (t*Δy)`

  By splitting we can alternate between two systems

    `ⅆ x t = f t (x t) y₀`
    and
    `ⅆ x t = ∂ (f t (x t)) y₀ (t*Δy)`

  The idea is to find such `Δy` after one round than the solution satisfies the constraint

-/
theorem odeSolveSemiImplicit_evolve_and_project {X Y} [Vec X] [Vec Y]
  (f : ℝ → X → Y → X) (g : ℝ → X → Y → Y)
  (Δt : ℝ) (x₀ : X) (y₀ : Y)
  :
  odeSolveSemiImplicit f g Δt x₀ y₀
  =
  let step (n : ℕ) := λ (x,y) =>
    let Δt' := Δt/n

    let x' := odeSolve (f · · y) Δt' x

    -- It is not intirelly clear what the general form of the correction term should look like
    -- This seems like a good choice
    let dy := (λ dy => g t (x' + Δt'*Δt'/2 * ∂ (f t x') y dy) (y + Δt' * dy))⁻¹ 0

    -- Alternativelly we can minimize the residual insted of doing an exact solve.
    -- For non-linear problems exact solution might not be possible.
    -- let Δy := argmin Δy', ∥g t (x' + Δt' * ∂ (f t x') y Δy') (y + Δy')∥²

    (x' + Δt'*Δt'/2 * ∂ (f t x') y dy, y + Δt' * dy)
  limit λ n => (step n)^[n] (x₀, y₀)
  := sorry_proof


/-- Solution of differential equation `ẋ = f t x` with a constraint `g t x = 0`.
This equates to solving the following semi-implicit differential-algebraic equation:
`
  ⅆ x t = f t (x t) + ∂† (g t) (x t) μ
      0 = g t x
`
Where `∂† (g t) (x t) μ` is a modification to the original ODE, with `μ` as a Lagrange multiplier,
allowing for the solution to satisfy the constraint.
-/
noncomputable
def odeSolveConstrained {X Y} [SemiHilbert X] [SemiHilbert Y]
  (f : ℝ → X → X) (g : ℝ → X → Y)
  (t : ℝ) (x₀ : X)
  : X
  :=
  (odeSolveSemiImplicit (λ t x μ => f t x + ∂† (g t) x μ) (λ t x y => g t x) t x₀ 0).1

noncomputable
def odeSolveConstrained' {X Y} [SemiHilbert X] [SemiHilbert Y]
  (f : ℝ → X → X) (g : ℝ → X → Y)
  (t : ℝ) (x₀ : X) (y₀ : Y)
  : X × Y
  :=
  (odeSolveSemiImplicit (λ t x y => f t x + ∂† (g t) x y) (λ t x _ => g t x) t x₀ y₀)


/-- A constrained ODE is a normal ODE if the constraint is solvable at every time and point.

The constraint `valid_constraint` is roughly saying that for every time `t` and point `x`:
  1. We can find the Lagrange multiplier `μ` used to correcly modify the unconstrained ODE
  2. The jacobian of the constraint function `J := ∂ (g t) x` has full rank
  3. The square jacobian of the constraint function, `J := ∂ (g t) x`, has invertible square i.e. `J ∘ J†` is invertible matrix
-/
theorem odeSolveConstrained_as_odeSolve {X Y} [SemiHilbert X] [SemiHilbert Y]
  (f : ℝ → X → X) (g : ℝ → X → Y) (t₀ : ℝ)
  (valid_constraint : ∀ t x, let J := ∂ (g t) x; IsInv (J ∘ J†))
  :
  odeSolveConstrained f g
  =
  let solveConstraint t x :=
    -- let J  := ∂ (g t) x
    -- solve μ, J (J† μ) = - J (f t x)
    (λ μ =>
      let J := ∂ (g t) x
      J (J† μ) + J (f t x))⁻¹ 0
  let f' t x :=
    let μ := solveConstraint t x
    f t x + ∂† (g t) x μ
  odeSolve f'
  :=
  sorry_proof



theorem odeSolveConstrained_evolve_and_project {X Y} [SemiHilbert X] [SemiHilbert Y]
  (f : ℝ → X → X) (g : ℝ → X → Y) (Δt : ℝ) (x₀ : X)
  :
  odeSolveConstrained f g Δt x₀
  =
  let step (n : ℕ) := λ x =>
    let Δt' := Δt/n

    let x' := odeSolve f Δt' x

    let y := (λ y => g t (x' + Δt' * ∂† (g t) x' y))⁻¹ 0

    x' + Δt' * ∂† (g t) x y

  limit λ n => (step n)^[n] x₀
  := sorry_proof


/-- This is usefull when we want to reuse the Lagrange multiplier `y` from the previous time step -/
theorem odeSolveConstrained'_evolve_and_project {X Y} [SemiHilbert X] [SemiHilbert Y]
  (f : ℝ → X → X) (g : ℝ → X → Y) (Δt : ℝ) (x₀ : X) (y₀ : Y)
  :
  odeSolveConstrained' f g Δt x₀ y₀
  =
  let step (n : ℕ) := λ (x,_) =>
    let Δt' := Δt/n

    let x' := odeSolve f Δt' x

    let y := (λ y => g t (x' + Δt' * ∂† (g t) x' y))⁻¹ 0

    (x' + Δt' * ∂† (g t) x y, y)

  limit λ n => (step n)^[n] (x₀,y₀)
  := sorry_proof


/-- This is usefull when we want to reuse the Lagrange multiplier `y` from the previous time step -/
theorem odeSolveConstrained'_evolve_and_reflect {X Y} [SemiHilbert X] [SemiHilbert Y]
  (f : ℝ → X → X) (g : ℝ → X → Y) (Δt : ℝ) (x₀ : X) (y₀ : Y)
  :
  odeSolveConstrained' f g Δt x₀ y₀
  =
  let step (n : ℕ) := λ (x,_) =>
    let Δt' := Δt/n

    let x' := odeSolve f Δt' x

    let y := (λ y => g t (x' + Δt' * ∂† (g t) x' y))⁻¹ 0

    (x' + Δt' * ∂† (g t) x y, y)

  limit λ n => (step n)^[n] (x₀,y₀)
  := sorry_proof
