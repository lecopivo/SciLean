import SciLean.Core.CoreFunctions
-- import SciLean.Solver.Solver

namespace SciLean

-- This file contains theorems and definitions that should be sorted and moved somewhere else

theorem invFun_as_argmin {X Y} [Nonempty X] [Hilbert X] [Hilbert Y] (f : X → Y) (y : Y) (hf : IsInv f)
  : f⁻¹ y = argmin x, ‖f x - y‖² := sorry_proof

theorem hold_fun_swap {α β} (f : α → β) (x : α)
  : f (hold x) = hold (f x) := by unfold hold; rfl

theorem hold_arg_swap {α β} (f : α → β) (x : α)
  : hold f x = hold (f x) := by unfold hold; rfl
