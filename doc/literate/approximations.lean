import SciLean
import SciLean.Tactic.ConvIf
open SciLean


/-!

==============
Approximations
==============

Scientific computing is full of approximations. SciLean attempts to provide
tools to manage these approximations and easily swap between them.

As a starting example we will look into computing the square root function.
Looking at wikipedia there are two basic methods: Babylonian_  and Bakhshali_.

.. _Babylonian: https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Babylonian_method
.. _Bakhshali: https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Bakhshali_method

The Babylonian method computes :math:`\sqrt{y}` from an initial guess :math:`x_0`
with an iterative process

.. math:: x_{n+1} = \frac{x_n + \frac{y}{x_n}}{2}

In code

-/

def sqrtBabylonian (n : Nat) (x₀ : ℝ) (y : ℝ) : ℝ :=
match n with
| 0   => x₀
| n+1 => sqrtBabylonian n ((x₀ + y/x₀)/2) y

/-!

The Bakhshali method computes :math:`\sqrt{y}` from an initial guess :math:`x_0`
with an iterative process

.. raw:: html

  \begin{align}
    a_n &= \frac{y - x_n^2}{2 x_n} \\
    b_n &= x_n + a_n \\
    x_{n+1} &= b_n - \frac{a_n^2}{2b_n}
  \end{align}


In code

-/

def sqrtBakhshali (n : Nat) (x₀ : ℝ) (y : ℝ) : ℝ :=
  match n with
  | 0 => x₀
  | n+1 =>
    let aₙ := (y - x₀*x₀)/(2*x₀)
    let bₙ := x₀ + aₙ
    let x₁ := bₙ - aₙ*aₙ/(2*bₙ)
    sqrtBakhshali n x₁ y

/-!
Let's test it out to compute :math:`\sqrt{2} = 1.41421356237\dots`
-/
#eval sqrtBabylonian 2 1 2 -- 1.416667
#eval sqrtBakhshali 2 1 2  -- 1.414214

/-!

Already at two steps Bakhshali method computes :math:`\sqrt{2}` correctly to
all the digits that are displayed.


Sqrt Specification
------------------

Because Lean is a proof assistant it allows us to define the square root
function precisely. The downside is that such function will be noncomputable.
This might sound completely pointless, how it is useful to define a function
that we can not run? The advantage is that we can disentangle the program
specification from its implementation.

The square root function is defined in mathlib_, we do not provide the
full definition here just

.. _mathlib: https://leanprover-community.github.io/mathlib_docs/data/real/sqrt.html#real.sqrt

 -/
noncomputable
def real.sqrt (x : ℝ) : ℝ := sorry
  --Possible noncomputable definition
  -- if x > 0 then
  --   inf { y // x < y * y }     -- infimum of a set is noncomputable
  -- else
  --   0

/-!

(TODO: Note somewhere that we assume that we have reals with computable + - * / <
  This either opens up a can of worms about consistency or floating point arithmetics.
  And I do not want to get into that right now ...)

The `real.sqrt` function satisfies two main properties. The first one,
called `real.mul_self_sqrt`_, for non-negative :math:`x` we have
:math:`\sqrt{x} \sqrt{x} = x`. The second one, called `real.sqrt_eq_zero_of_nonpos`_,
for negative :math:`x` the :math:`\sqrt{x}` is defined to be zero. In math class
square root of negative number is usually not defined, however in type theory
this does not work so well. This is similar to division by zero, in
Lean we have `1/0 = 0`, you can read about this more on Kevin Buzzard's page_.

.. _page: https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/

.. _`real.sqrt_eq_zero_of_nonpos`: https://leanprover-community.github.io/mathlib_docs/data/real/sqrt.html#real.sqrt_eq_zero_of_nonpos

.. _`real.mul_self_sqrt`:  https://leanprover-community.github.io/mathlib_docs/data/real/sqrt.html#real.mul_self_sqrt

 -/

theorem real.mul_self_sqrt {x : ℝ} (h : 0 ≤ x)
  : real.sqrt x * real.sqrt x = x := sorry

@[simp]
theorem real.sqrt_eq_zero_of_nonpos {x : ℝ} (h : ¬(0 ≤ x))
  : real.sqrt x = 0 := sorry

/-!

In particular, we can proof that the Babylonian and Bakhshali method
converge to the square root. Again we omit the proofs here again, but
it is well in the capability of Lean and mathlib to do so.

 -/

theorem sqrtBabylonian.limit {x : ℝ} (y₀ : ℝ) (hy : y₀ ≥ 0) (hx : 0 ≤ x)
  : real.sqrt x = limit λ n => sqrtBabylonian n y₀ x := sorry

theorem sqrtBakhshali.limit {x : ℝ} (y₀ : ℝ) (hy : y₀ ≥ 0) (hx : 0 ≤ x)
  : real.sqrt y = limit λ n => sqrtBakhshali n x₀ y := sorry

/-!

To build an approximation, we state `approx sqrtApprox := real.sqrt` followed
by instructions how to construct such approximation. The type of `sqrtApprox` is
`Approx real.sqrt`, which is an object holding couple of useful informations
about the approximation:

  1. Parameters to control the accuracy of the approximation.
  2. Options to switch between different approximations.
  3. Under what conditions this approximation is actually valid.

Here is the Lean code to generate the approximation
 -/

approx sqrtApprox := real.sqrt
by
  conv =>
    trace_state
    enter [1] -- Step into `Approx ...`
    enter [x] -- introduce the argument `x`

    if h : 0 ≤ x then
      -- For positive `x` we apply the Babylonian method
      rw [sqrtBabylonian.limit (x/2) (sorry) h]
    else
      -- For negative `x` we know the result is zero
      rw [real.sqrt_eq_zero_of_nonpos h]

  -- We pick 4 steps as default
  approx_limit 4; intro n

/-!

(TODO: Add parameter to switch between Babylonian and Bakhshali.)

To get the value of an approximation we need to call `.val!`

 -/

#eval sqrtApprox.val 2
