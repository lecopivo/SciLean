import SciLean.Data.IdxType.Fold
import SciLean.Data.IndexType.SumProduct

namespace SciLean

variable {I : Type u} {α : Type}  {n} [IdxType I n] [IdxType.Fold.{u,0,0} I Id]

namespace IdxType

@[specialize, inline]
def sum [Zero α] [Add α] (f : I → α) : α :=
  IdxType.foldl (IndexType.Range.full (I:=I)) (init := 0) (fun i s => s + f i)


open Lean.TSyntax.Compat in
/-- `∑ᴵ (i : I), f i` is sum over indextype `I` i.e. has instance `IdxType I n`. -/
macro " ∑ᴵ " xs:Lean.explicitBinders ", " b:term:66 : term =>
  Lean.expandExplicitBinders ``IdxType.sum xs b

@[app_unexpander sum] def unexpandIdxTypeSum : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => $b) =>
    `(∑ᴵ $x:ident, $b)
  | `($(_) fun $x:ident $xs:ident* => $b) =>
    `(∑ᴵ $x:ident, fun $xs* => $b)
  | `($(_) fun ($x:ident : $ty:term) => $b) =>
    `(∑ᴵ ($x:ident : $ty), $b)
  | _  => throw ()

set_option pp.universes true

abbrev min [Min α] [Inhabited α] (f : I → α) : α :=
  IdxType.reduce (IndexType.Range.full (I:=I)) f (Min.min · ·)

abbrev max [Max α] [Inhabited α] (f : I → α) : α :=
  IdxType.reduce (IndexType.Range.full (I:=I)) f (Max.max · ·)

abbrev argMinVal {I α : Type*} {n}
    [IdxType I n] [IdxType.Fold' I]
    [LE α] [DecidableLE α] [Inhabited I]
    (f : I → α) : (I×α) :=
  IdxType.reduceD (IndexType.Range.full (I:=I))
    (fun i => (i,f i)) (fun (i,xi) (j,xj) => if xi ≤ xj then (i,xi) else (j,xj))
    (default, f default)

abbrev argMaxVal {I α : Type*} {n}
    [IdxType I n] [IdxType.Fold' I]
    [LE α] [DecidableLE α] [Inhabited I]
    (f : I → α) : (I×α) :=
  IdxType.reduceD (IndexType.Range.full (I:=I))
    (fun i => (i,f i)) (fun (i,xi) (j,xj) => if xi ≤ xj then (j,xj) else (i,xi))
    (default, f default)

abbrev argMin {I α : Type*} {n}
    [IdxType I n] [IdxType.Fold' I]
    [LE α] [DecidableLE α] [Inhabited I]
    (f : I → α) : I := (argMinVal f).1

abbrev argMax {I α : Type*}
    [IdxType I n] [IdxType.Fold' I]
    [LE α] [DecidableLE α] [Inhabited I]
    (f : I → α) : I := (argMaxVal f).1
