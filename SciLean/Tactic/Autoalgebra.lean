import SciLean.Algebra

import SciLean.Prelude
import SciLean.Tactic.RemoveLambdaLet
import SciLean.Tactic.Autodiff

import Lean
import Lean.Meta.Basic
import Lean.Elab.Tactic.Basic

namespace Autoalgebra

  variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]

   theorem add_zero (x : X) : x + 0 = x := sorry
   theorem zero_add (x : X) : 0 + x = x := sorry

   theorem mul_one (x : ℝ) : x * 1 = x := sorry
   theorem one_mul (x : X) : (1:ℝ) * x = x := sorry

   theorem add_same_1 (a b : ℝ) (x : X) : a*x + b*x = (a+b)*x := sorry
   theorem add_same_2 (a : ℝ) (x : X) : a*x + x = (a+1)*x := sorry
   theorem add_same_3 (a : ℝ) (x : X) : x + a*x = (1+a)*x := sorry
   theorem add_same_4 (x : X) : x + x = (2:ℝ)*x := sorry

   theorem smul_smul_mul (a b : ℝ) (x : X) : a * (b * x) = (a*b) * x := sorry

   theorem prod_sum (x x' : X) (y y' : Y) : (x, y) + (x', y') = (x + x', y + y') := sorry

end Autoalgebra

syntax "autoalgebra_step" : tactic --

macro_rules
  | `(tactic| autoalgebra_step) => `(tactic| rw [Autoalgebra.add_zero])

macro_rules
  | `(tactic| autoalgebra_step) => `(tactic| rw [Autoalgebra.zero_add])

-- macro_rules
--   | `(tactic| autoalgebra_step) => `(tactic| rw [Autoalgebra.prod_sum])

macro "autoalgebra" : tactic => `(repeat autoalgebra_step)

