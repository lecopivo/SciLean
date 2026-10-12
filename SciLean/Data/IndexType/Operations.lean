module

public import SciLean.Data.IndexType.Fold


public import Mathlib.Data.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Abel

@[expose] public section

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

@[app_unexpander sum] meta def unexpandIndexTypeSum : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => $b) =>
    `(∑ᴵ $x:ident, $b)
  | `($(_) fun $x:ident $xs:ident* => $b) =>
    `(∑ᴵ $x:ident, fun $xs* => $b)
  | `($(_) fun ($x:ident : $ty:term) => $b) =>
    `(∑ᴵ ($x:ident : $ty), $b)
  | _  => throw ()

theorem sum_eq_finset_sum {α} [AddCommMonoid α] (f : I → α) :
  ∑ᴵ i, f i = Finset.univ.sum f := sorry_proof

/-- `α` with the addition `x + y - a` which is a commutative monoid with zero `a`. -/
private def ShiftedAdd (α : Type v) (_a : α) := α

private instance {α : Type v} [AddCommGroup α] (a : α) : AddCommMonoid (ShiftedAdd α a) where
  zero := (a : α)
  add := fun (x y : α) => x + y - a
  add_assoc := (by intros; abel : ∀ x y z : α, (x + y - a) + z - a = x + (y + z - a) - a)
  zero_add := (by intros; abel : ∀ x : α, a + x - a = x)
  add_zero := (by intros; abel : ∀ x : α, x + a - a = x)
  add_comm := (by intros; abel : ∀ x y : α, x + y - a = y + x - a)
  nsmul := fun n (x : α) => n • (x - a) + a
  nsmul_zero := (by intros; simp : ∀ x : α, (0 : ℕ) • (x - a) + a = a)
  nsmul_succ := (by intros; rw [succ_nsmul]; abel :
    ∀ (n : ℕ) (x : α), (n + 1) • (x - a) + a = (n • (x - a) + a) + x - a)

/-- Folding `s + f i` starting from `a` gives `a + ∑ i, f i`. -/
theorem fold_add_eq_add_sum {α} [AddCommGroup α] (a : α) (f : I → α) :
    IndexType.fold .full (init := a) (fun i s => s + f i) = a + Finset.univ.sum f := by
  have h := sum_eq_finset_sum (α := ShiftedAdd α a) (fun i => (f i + a : α))
  have hs : ∀ s : Finset I,
      (s.sum (M := ShiftedAdd α a) (fun i => (f i + a : α)) : α) = a + s.sum f := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => show a = a + 0; simp
    | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      refine (Finset.sum_insert (M := ShiftedAdd α a) (f := fun i => (f i + a : α)) hj).trans ?_
      show (f j + a) + _ - a = _
      rw [ih]; abel
  rw [hs] at h
  rw [← h]
  show _ = IndexType.fold .full (init := a) (fun i s => s + (f i + a) - a)
  congr; funext i s; abel


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
@[app_unexpander min] meta def unexpandIndexTypeMin : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:funBinder => $b) =>
    `(minᴵ $x, $b)
  | _  => throw ()


open Lean.Parser.Term in
/-- `argMinᴵ (i : I), f i` returns index at which `f` is minimal over index type `I`.-/
macro "argMinᴵ " x:funBinder ", " b:term:66 : term => `(IndexType.argMin fun $x => $b)

open Lean.Parser.Term in
@[app_unexpander argMin] meta def unexpandIndexTypeArgMin : Lean.PrettyPrinter.Unexpander
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
@[app_unexpander max] meta def unexpandIndexTypeMax : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:funBinder => $b) =>
    `(maxᴵ $x, $b)
  | _  => throw ()


open Lean.Parser.Term in
/-- `argMaxᴵ (i : I), f i` returns index at which `f` is maximal over index type `I`.-/
macro "argMaxᴵ " x:funBinder ", " b:term:66 : term => `(IndexType.argMax fun $x => $b)

open Lean.Parser.Term in
@[app_unexpander argMax] meta def unexpandIndexTypeArgMax : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:funBinder => $b) =>
    `(argMaxᴵ $x, $b)
  | _  => throw ()
