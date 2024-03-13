import LeanColls
import SciLean.Util.SorryProof

open LeanColls

instance : IndexType Unit where
  card := 1
  toFin _ := 0
  fromFin _ := ()

instance : LawfulIndexType Unit where
 toFin_leftInv  := by intro x; aesop
 toFin_rightInv := by intro x; rfl

instance : LawfulIndexType (Fin n) where
  toFin_leftInv := by intro x; rfl
  toFin_rightInv := by intro x; rfl

open Set

instance (a b : Int) : IndexType (Icc a b) where
  card := ((b + 1) - a).toNat
  toFin i := ⟨(i.1 - a).toNat, sorry_proof⟩
  fromFin i := ⟨a + i.1, sorry_proof⟩

instance (a b : Int) : LawfulIndexType (Icc a b) where
  toFin_leftInv := by intro x; simp[IndexType.toFin, IndexType.fromFin]
  toFin_rightInv := by intro x; sorry_proof

instance (a b : Int) : IndexType (Ioo a b) where
  card := (b - (a + 1)).toNat
  toFin i := ⟨(i.1 - (a + 1)).toNat, sorry_proof⟩
  fromFin i := ⟨(a + 1) + i.1, sorry_proof⟩

instance (a b : Int) : LawfulIndexType (Ioo a b) where
  toFin_leftInv := by intro x; simp[IndexType.toFin, IndexType.fromFin]
  toFin_rightInv := by intro x; sorry_proof

instance (a b : Int) : IndexType (Ioc a b) where
  card := ((b + 1) - (a+1)).toNat
  toFin i := ⟨(i.1 - (a + 1)).toNat, sorry_proof⟩
  fromFin i := ⟨(a + 1) + i.1, sorry_proof⟩

instance (a b : Int) : LawfulIndexType (Ioc a b) where
  toFin_leftInv := by intro x; simp[IndexType.toFin, IndexType.fromFin]
  toFin_rightInv := by intro x; sorry_proof

instance (a b : Int) : IndexType (Ico a b) where
  card := (b - a).toNat
  toFin i := ⟨(i.1 - a).toNat, sorry_proof⟩
  fromFin i := ⟨a + i.1, sorry_proof⟩

instance (a b : Int) : LawfulIndexType (Ico a b) where
  toFin_leftInv := by intro x; simp[IndexType.toFin, IndexType.fromFin]
  toFin_rightInv := by intro x; sorry_proof


namespace SciLean
-- use lean colls
export LeanColls (IndexType IndexType.card IndexType.univ IndexType.toFin IndexType.fromFin LawfulIndexType)
end SciLean

namespace IndexType


variable {ι : Type v} [IndexType ι]

@[specialize] def sum {α : Type u} [Zero α] [Add α] (f : ι → α) : α :=
  Fold.fold (β:=α) (C:=IndexType.Univ ι) (τ:=ι) (IndexType.univ ι) (fun (s : α) (i : ι) => s + f i) (0 : α)

def reduceMD {m} [Monad m] (f : ι → α) (op : α → α → m α) (default : α) : m α := do
  let n := IndexType.card ι
  if n = 0 then
    return default
  let mut a := f (IndexType.fromFin ⟨0,sorry_proof⟩)
  for i in [1:n] do
    a ← op a (f (IndexType.fromFin ⟨i,sorry_proof⟩))
  return a

def reduceD (f : ι → α) (op : α → α → α) (default : α) : α :=
  let n := IndexType.card ι
  if n = 0 then
    default
  else
    Id.run do
    let mut a := f (IndexType.fromFin ⟨0,sorry_proof⟩)
    for i in [0:n-1] do
      let i : Fin n := ⟨i+1, sorry_proof⟩
      a := op a (f (IndexType.fromFin i))
    a
abbrev reduce [Inhabited α] (f : ι → α) (op : α → α → α) : α :=
  reduceD f op default

open Lean.TSyntax.Compat in
macro " ∑ " xs:Lean.explicitBinders ", " b:term:66 : term => Lean.expandExplicitBinders ``sum xs b

@[app_unexpander sum] def unexpandSum : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => $b) =>
    `(∑ $x:ident, $b)
  | `($(_) fun $x:ident $xs:ident* => $b) =>
    `(∑ $x:ident, fun $xs* => $b)
  | `($(_) fun ($x:ident : $ty:term) => $b) =>
    `(∑ ($x:ident : $ty), $b)
  | _  => throw ()


@[specialize] def product {α} [One α] [Mul α] {ι} [IndexType ι] (f : ι → α) : α :=
  Fold.fold (IndexType.univ ι) (fun s i => s * f i) 1

open Lean.TSyntax.Compat in
macro " ∏ " xs:Lean.explicitBinders ", " b:term:66 : term => Lean.expandExplicitBinders ``product xs b

@[app_unexpander product] def unexpandProduct : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => $b) =>
    `(∏ $x:ident, $b)
  | `($(_) fun $x:ident $xs:ident* => $b) =>
    `(∏ $x:ident, fun $xs* => $b)
  | `($(_) fun ($x:ident : $ty:term) => $b) =>
    `(∏ ($x:ident : $ty), $b)
  | _  => throw ()
