import SciLean
import SciLean.Tactic.ConvIf
open SciLean


/-!

==============
Approximations
==============

Scientific computing is full of approximations. SciLean attempts to provide
tools to manage these approximations and easity swap between them.

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

Let's state the existence of square root for positive real numbers
 -/
theorem sqrt_exists : ∀ (y : ℝ), y ≥ 0 → ∃ (x : ℝ), x ≥ 0 ∧ x * x = y := sorry

/-!
We omit the proof of this theorem here.

Now we can define the noncomputable version of `sqrt` that returns the 
square root for positive numbers and zero for negative numbers.
 -/
noncomputable
def sqrt (y : ℝ) : ℝ := sorry

theorem sqrt_on_pos (y : ℝ) :   y ≥ 0  → sqrt y * sqrt y = y := sorry
theorem sqrt_on_neg (y : ℝ) : ¬(y ≥ 0) → sqrt y = 0 := sorry

/-!

Here we just postulate the existence of the square root function but
its full definition can be found in mathlib_.

.. _mathlib: https://leanprover-community.github.io/mathlib_docs/data/real/sqrt.html


In particular, we can proof that the Babylonian and Bakhshali method 
converge to the square root
 -/

theorem sqrtBabylonian.limit (x₀ y : ℝ) : x₀ ≥ 0 → y ≥ 0 →
  sqrt y = limit λ n => sqrtBabylonian n x₀ y := sorry

theorem sqrtBakhshali.limit (x₀ y : ℝ) : x₀ ≥ 0 → y ≥ 0 →
  sqrt y = limit λ n => sqrtBakhshali n x₀ y := sorry

/-!
We omit these proofs again as it is not what were are after right now.
 -/

approx sqrtApprox := sqrt
by 
  trace_state
  conv => 
    enter [1,y] 

    if h : y≥0 then 
      rw [sqrtBabylonian.limit 1 y (by native_decide) h]
    else
      rw [sqrt_on_neg y h]

  
  approx_limit 4; intro n

/-!

To get the value of an approximation we need to call `.val!` 

 -/
#eval sqrtApprox.val! 2
