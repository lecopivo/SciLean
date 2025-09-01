import Mathlib.Logic.Function.Basic
import Mathlib.Order.WellFounded

import SciLean.Util.SolveFun
import SciLean.Analysis.Scalar.FloatAsReal
import SciLean.Analysis.AdjointSpace.Adjoint

namespace SciLean

open Lean Parser Term in
macro (name:=argMinStx) "argmin" xs:funBinder* ", " b:term : term => do
  `(Function.argmin ↿fun $xs* => $b)

@[app_unexpander Function.argmin]
def unexpandArgMin : Lean.PrettyPrinter.Unexpander
  | `($(_) ↿fun $xs* => $b) =>
    `(argmin $xs*, $b)
  | _  => throw ()

set_option linter.unusedVariables false in
theorem solve_eq_argmin_norm2
    (R : Type*) [RealScalar R]
    {X : Type*} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X]
    {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace R Y] [CompleteSpace Y]
    {f : X → Y} {y : Y} (hf : HasUniqueSolution (fun x => f x = y)) :
    (solve x, f x = y) = argmin x, ‖f x - y‖₂²[R] := sorry_proof
