import Mathlib.Order.WellFounded

import SciLean.Data.Curry
import SciLean.Core.Objects.Vec
import SciLean.Core.Objects.SemiInnerProductSpace
import SciLean.Core.Objects.Scalar

namespace SciLean


structure HasMinimum {α β} [LT β] (f : α → β) : Prop where
  has_min : ∃ a, ∀ a', a ≠ a' → f a < f a'


/-- Finds `x : α` that minimizes of `f x`. 

Return default value of `α` if such `x` does not exist.
-/
noncomputable
def argMin {α β} [ne : Nonempty α] [LT β] (f : α → β) : α :=
  have := Classical.propDecidable
  if h : HasMinimum f then
    Classical.choose h.has_min
  else
    (Classical.inhabited_of_nonempty ne).default


noncomputable
def argMinN {F : Type _} {Xs Y : outParam (Type _)} [UncurryAll F Xs Y] [Nonempty Xs] [LT Y] (f : F /- Xs → ... → Prop -/) : Xs := argMin (uncurryAll f)


open Lean Parser Elab Term in
/-- `argmin x y, f x y` returns `(x,y)` that minimizes `f x y`. 

Return default values if such `x,y` does not exist.
-/
macro "argmin" xs:funBinder* ", " b:term : term => do
  `(argMinN fun $xs* => $b)


@[app_unexpander argMinN] def unexpandArgMinN : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $xs* => $b) =>
    `(argmin $xs*, $b)
  | _  => throw ()


--------------------------------------------------------------------------------

structure HasMaximum {α β} [LT β] (f : α → β) : Prop where
  has_max : ∃ a, ∀ a', a ≠ a' → f a' < f a


/-- Finds `x : α` that maximizes of `f x`. 

Return default value of `α` if such `x` does not exist.
-/
noncomputable
def argMax {α β} [ne : Nonempty α] [LT β] (f : α → β) : α :=
  have := Classical.propDecidable
  if h : HasMaximum f then
    Classical.choose h.has_max
  else
    (Classical.inhabited_of_nonempty ne).default


noncomputable
def argMaxN {F : Type _} {Xs Y : outParam (Type _)} [UncurryAll F Xs Y] [Nonempty Xs] [LT Y] (f : F /- Xs → ... → Prop -/) : Xs := argMax (uncurryAll f)


open Lean Parser Elab Term in
/-- `argmax x y, f x y` returns `(x,y)` that maximizes `f x y`. 

Return default values if such `x,y` does not exist.
-/
macro "argmax" xs:funBinder* ", " b:term : term => do
  `(argMaxN fun $xs* => $b)


@[app_unexpander argMaxN] def unexpandArgMaxN : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $xs* => $b) =>
    `(argmax $xs*, $b)
  | _  => throw ()


--------------------------------------------------------------------------------


open Function
theorem invFun_as_min_norm2 {R} [RealScalar R] {X Y} [Nonempty X] [SemiInnerProductSpace R Y]
  (f : X → Y) (y : Y) (hf : Bijective f) 
  : invFun f y = argmin x, ‖f x - y‖₂²[R] := sorry_proof

