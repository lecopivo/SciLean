import SciLean.Core.Rand.Rand
import SciLean.Core.Rand.Condition

import Mathlib.MeasureTheory.Constructions.Prod.Basic

namespace SciLean

open MeasureTheory
variable
  {R} [RealScalar R]
  {X Y} [MeasureSpace X] [MeasureSpace Y]


/-- Special form of bind for `Rand` for which it is easy to compute conditional probabilities and
probability densities. Most likely you want to use this bind when defining probabilistic model. -/
def Rand.modelBind (x : Rand X) (f : X → Rand Y) : Rand (X×Y) := do
  let x' ← x
  let y' ← f x'
  return (x',y')


----------------------------------------------------------------------------------------------------
-- Notation ----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- we can't use do notation because Rand is not a monad right now (because of the [MeasurableSpace X] argument)
-- this is a small hack to recover it a bit
open Lean.Parser Term in
syntax withPosition("let" funBinder " ~ " term (semicolonOrLinebreak ppDedent(ppLine) term)?) : term
macro_rules
  | `(let $x ~ $y; $b) => do Pure.pure (← `(SciLean.Rand.modelBind $y (fun $x => $b))).raw
  | `(let $_ ~ $y) => `($y)

open Lean Parser
@[app_unexpander SciLean.Rand.modelBind] def unexpandRandBind : Lean.PrettyPrinter.Unexpander

| `($(_) $y $f) =>
  match f.raw with
  | `(fun $x:term => $b) => do
    let s ←
      `(let $x ~ $y
        $b)
    Pure.pure s.raw
  | _ => throw ()

| _ => throw ()




----------------------------------------------------------------------------------------------------
-- Pdf, measure, condition -------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


@[simp, ftrans_simp]
theorem modelBind_condition (r : Rand X) (f : X → Rand Y) (x' : X) :
    (let x ~ r; f x).conditionFst x'
    =
    f x' := sorry_proof

@[simp, ftrans_simp]
theorem modelBind_pdf (r : Rand X) (f : X → Rand Y) :
    (let x ~ r; f x).pdf R (volume : Measure (X×Y))
    =
    fun xy => (r.pdf R volume xy.1) * (f xy.1).pdf R volume xy.2 := sorry_proof

@[simp, ftrans_simp]
theorem modelBind_pdf_prod [MeasurableSpace X] [MeasurableSpace Y]
    (r : Rand X) (f : X → Rand Y) (μ : Measure X) (ν : Measure Y) :
    (let x ~ r; f x).pdf R (μ.prod ν)
    =
    fun xy => (r.pdf R μ xy.1) * (f xy.1).pdf R ν xy.2 := sorry_proof
