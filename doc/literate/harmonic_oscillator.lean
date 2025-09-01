import SciLean.Mechanics
import SciLean.Operators.ODE
-- import SciLean.Solver
-- import SciLean.Tactic.LiftLimit
-- import SciLean.Tactic.FinishImpl
import SciLean.Solver.Solver

open SciLean


/-!

==============================
Harmonic Oscillator in SciLean
==============================

Let's demonstrate basic capabilities of SciLean on the simulation of
harmonic oscillator.

The energy of harmonic oscillator is

.. math:: H(x,p) = \frac{1}{2m} p^2 + \frac{k}{2} x^2

As a Lean code, this is:

-/

def H (m k : ℝ) (x p : ℝ) := 1/(2*m) * ∥p∥² + k/2 * ∥x∥²


/-!

To compute a derivative of a function `f : ℝ → ℝ`

.. math:: \frac{\partial}{\partial x} f(x) \qquad \text{or} \qquad \frac{\partial}{\partial x'}\bigg\rvert_{x'=x} f(x')

we write `∇ x, f x` or `λ x => ∇ (x':=x), f x'`.

The derivative w.r.t position of the Hamiltonian is
-/

#check (λ m k x p => ∇ (x':=x), H m k x' p)
  rewrite_by (simp[H,gradient]; trace_state) /- .unfold -/


/-!

And the derivative w.r.t momentum of the Hamiltonian is
 -/

#check (λ m k x p => ∇ (p':=p), H m k x p')
  rewrite_by (simp[H,gradient,hold]; trace_state) /- .unfold -/


/-!

To run a simulation means to numerically solve some differential equation.
Surprisingly, SciLean defines a function `ode_solve` that solves a generic
differential equation exactly

.. math:: \dot x = f(x) \qquad x(0) = x_0

The catch is that this function is not computable. This means there is
no universal algorithm that would give you a solution of the above
differential equation for any `f`. Nonetheless, `ode_solve` is well
defined and in SciLean we use it to specify what kind of program we
want to build.

Let's have a look at the type signature of `ode_solve`

-/

#check λ {X} [Vec X] (f : X → X) (t : ℝ) (x₀ : X)  => ode_solve f t x₀ /- .unfold -/

/-!

For harmonic oscillator, the evolution is given by Hamilton's equations

.. raw:: html

  \begin{align}
  \dot x &= \frac{\partial H}{\partial p} \\
  \dot p &= - \frac{\partial H}{\partial x}
  \end{align}

Thus the function `f` that needs to be provided to `ode_solve` is
`λ (x,p) => (∇ (p':=p), H x p', - ∇ (x':=x), H x' p)`

-/

#check λ m k (x,p) => (∇ (p':=p), H m k x p', - ∇ (x':=x), H m k x' p) /- .unfold -/


/-!

Now we turn in to a very interesting style of programming. We provide
a specification and with a series of commands(tactics) we construct a runnable
program.

To run a simulation on a computer we want an implementation of a differential
equation solver i.e. we want a witness of `Impl (ode_solve f)`.

For harmonic oscillator this is

 -/

-- set_option trace.Meta.Tactic.simp.rewrite true in
approx solver (steps : Nat) := λ (m k : ℝ) =>
  (ode_solve λ (x,p) => (  ∇ (p':=p), H m k x p',
                         - ∇ (x':=x), H m k x' p))
by
  -- unfold Hamiltonian definition
  simp [H];

  -- compute gradients
  simp[gradient, hold];

  -- apply RK4 method
  rw [ode_solve_fixed_dt runge_kutta4_step]

  -- agree that we solve the original goal only approximately
  bubble_limit; sorry_proof; apply Approx.limit _ steps; intro n; simp


/-!

Run the simulation and do a simple plotting

 -/

def main : IO Unit := do

  let substeps := 1
  let m := 1.0
  let k := 10.0

  let evolve := (solver substeps).val m k

  let x₀ : ℝ := 1.0
  let p₀ : ℝ := 0.0
  let mut (x,p) := (x₀, p₀)

  for _ in [0:40] do

    (x, p) := evolve 0.1 (x, p)

    -- print
    for (j : Nat) in [0:20] do
      if j < 10*(x+1) then
        IO.print "o"
    IO.println ""

/-!

The actual run

 -/

#eval main /- .unfold -/
