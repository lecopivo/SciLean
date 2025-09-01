import SciLean.Data.IndexType.Fold


import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
-- import SciLean.Data.IndexType.SumProduct

namespace SciLean

variable {I : Type u} {α : Type v}  {n} [IndexType I n] [FoldM.{u,v,v} I Id]

namespace IndexType


/-- `sum f` returns sum of `f` over index type `I`. -/
@[specialize, inline]
def sum [Zero α] [Add α] (f : I → α) : α :=
  IndexType.fold (IndexType.Range.full (I:=I)) (init := 0) (fun i s => s + f i)


open Lean.TSyntax.Compat in
/-- `∑ᴵ (i : I), f i` is sum of values of `f` over the index type `I`.

There has to be an instance `IndexType I n` and `Fold I`. -/
macro " ∑ᴵ " xs:Lean.explicitBinders ", " b:term:66 : term =>
  Lean.expandExplicitBinders ``IndexType.sum xs b

@[app_unexpander sum] def unexpandIndexTypeSum : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => $b) =>
    `(∑ᴵ $x:ident, $b)
  | `($(_) fun $x:ident $xs:ident* => $b) =>
    `(∑ᴵ $x:ident, fun $xs* => $b)
  | `($(_) fun ($x:ident : $ty:term) => $b) =>
    `(∑ᴵ ($x:ident : $ty), $b)
  | _  => throw ()

theorem sum_eq_finset_sum {α} [AddCommMonoid α] (f : I → α) :
  ∑ᴵ i, f i = Finset.univ.sum f := sorry_proof


----------------------------------------------------------------------------------------------------
-- min ---------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

/-- `min f` returns minimum of `f` over index type `I`. -/
@[specialize, inline]
def min [Min α] [Top α] (f : I → α) : α :=
  IndexType.fold (IndexType.Range.full (I:=I)) (init:=(⊤:α)) (fun i m => Min.min (f i) m)

@[specialize, inline]
def argMinVal {I α : Type*} {n}
    [IndexType I n] [Fold I]
    [LE α] [DecidableLE α] [Top α] [Inhabited I]
    (f : I → α) : (I×α) :=
  IndexType.fold (IndexType.Range.full (I:=I))
    (init := (default, ⊤))
    (fun j (i,xi)  =>
      let xj := f j
      if xi ≤ xj then (i,xi) else (j,xj))

/-- `argMin f` returns index at which `f` is minimal over index type `I`. -/
@[specialize, inline]
def argMin {I α : Type*} {n}
    [IndexType I n] [Fold I]
    [LE α] [DecidableLE α] [Top α] [Inhabited I]
    (f : I → α) : I := (argMinVal f).1

open Lean.Parser.Term in
/-- `mᴵ (i : I), f i` returns minimum of `f` over index type `I`.

There has to be an instance `IndexType I n` and `Fold I`. -/
macro "minᴵ " x:funBinder ", " b:term:66 : term => `(IndexType.min fun $x => $b)

open Lean.Parser.Term in
@[app_unexpander min] def unexpandIndexTypeMin : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:funBinder => $b) =>
    `(minᴵ $x, $b)
  | _  => throw ()


open Lean.Parser.Term in
/-- `argMinᴵ (i : I), f i` returns index at which `f` is minimal over index type `I`.-/
macro "argMinᴵ " x:funBinder ", " b:term:66 : term => `(IndexType.argMin fun $x => $b)

open Lean.Parser.Term in
@[app_unexpander argMin] def unexpandIndexTypeArgMin : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:funBinder => $b) =>
    `(argMinᴵ $x, $b)
  | _  => throw ()



----------------------------------------------------------------------------------------------------
-- max ---------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

/-- `max f` returns maximum of `f` over index type `I`. -/
@[specialize, inline]
def max [Max α] [Bot α] (f : I → α) : α :=
  IndexType.fold (IndexType.Range.full (I:=I)) (init:=(⊥:α)) (fun i m => Max.max (f i) m)

@[specialize, inline]
def argMaxVal {I α : Type*} {n}
    [IndexType I n] [Fold I]
    [LE α] [DecidableLE α] [Inhabited I] [Bot α]
    (f : I → α) : (I×α) :=
  IndexType.fold (IndexType.Range.full (I:=I))
    (init := (default, ⊥))
    (fun j (i,xi)  =>
      let xj := f j
      if xi ≤ xj then (j,xj) else (i,xi))


/-- `argMax f` returns index at which `f` is maximal over index type `I`. -/
@[specialize, inline]
def argMax {I α : Type*} {n}
    [IndexType I n] [Fold I]
    [LE α] [DecidableLE α] [Inhabited I] [Bot α]
    (f : I → α) : I := (argMaxVal f).1

open Lean.Parser.Term in
/-- `mᴵ (i : I), f i` returns maximum of `f` over index type `I`.

There has to be an instance `IndexType I n` and `Fold I`. -/
macro "maxᴵ " x:funBinder ", " b:term:66 : term => `(IndexType.max fun $x => $b)

open Lean.Parser.Term in
@[app_unexpander max] def unexpandIndexTypeMax : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:funBinder => $b) =>
    `(maxᴵ $x, $b)
  | _  => throw ()


open Lean.Parser.Term in
/-- `argMaxᴵ (i : I), f i` returns index at which `f` is maximal over index type `I`.-/
macro "argMaxᴵ " x:funBinder ", " b:term:66 : term => `(IndexType.argMax fun $x => $b)

open Lean.Parser.Term in
@[app_unexpander argMax] def unexpandIndexTypeArgMax : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:funBinder => $b) =>
    `(argMaxᴵ $x, $b)
  | _  => throw ()
