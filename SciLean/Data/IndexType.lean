import LeanColls
import SciLean.Util.SorryProof
import SciLean.Tactic.RefinedSimp


open LeanColls

open Set

instance (a b : Int) : IndexType (Icc a b) where
  card := ((b + 1) - a).toNat
  toFin i := ⟨(i.1 - a).toNat,
    by
      cases i; case mk i lt =>
        simp at lt ⊢; simp (disch:=aesop) only [Int.toNat_of_nonneg, sub_lt_sub_iff_right]; omega⟩
  fromFin i := ⟨a + i.1, by cases i; case mk i lt => simp at lt ⊢; omega⟩
  fold := fun _ f init => Id.run do
    let mut x := init
    for i in [0:(b-a).toNat] do
      let i : Icc a b := ⟨a + i, sorry_proof⟩
      x := f x i
    return x

  foldM := fun _ f init => do
    let mut x := init
    for i in [0:(b-a).toNat] do
      let i : Icc a b := ⟨a + i, sorry_proof⟩
      x ← f x i
    return x

instance (a b : Int) : LawfulIndexType (Icc a b) where
  leftInv := by
    intro x
    simp only [IndexType.toFin, IndexType.fromFin]
    sorry_proof
  rightInv := by
    intro x
    simp only [IndexType.toFin, IndexType.fromFin, add_sub_cancel_left, Int.toNat_ofNat, Fin.eta]
  fold_eq_fold_toList := sorry_proof
  foldM_eq_fold := sorry_proof

-- instance (a b : Int) : IndexType (Ioo a b) where
--   card := (b - (a + 1)).toNat
--   toFin i := ⟨(i.1 - (a + 1)).toNat, sorry_proof⟩
--   fromFin i := ⟨(a + 1) + i.1, sorry_proof⟩

-- instance (a b : Int) : LawfulIndexType (Ioo a b) where
--   leftInv := by intro x; sorry_proof
--   rightInv := by intro x; sorry_proof

-- instance (a b : Int) : IndexType (Ioc a b) where
--   card := ((b + 1) - (a+1)).toNat
--   toFin i := ⟨(i.1 - (a + 1)).toNat, sorry_proof⟩
--   fromFin i := ⟨(a + 1) + i.1, sorry_proof⟩

-- instance (a b : Int) : LawfulIndexType (Ioc a b) where
--   leftInv := by intro x; sorry_proof
--   rightInv := by intro x; sorry_proof

-- instance (a b : Int) : IndexType (Ico a b) where
--   card := (b - a).toNat
--   toFin i := ⟨(i.1 - a).toNat, sorry_proof⟩
--   fromFin i := ⟨a + i.1, sorry_proof⟩

-- instance (a b : Int) : LawfulIndexType (Ico a b) where
--   leftInv := by intro x; sorry_proof
--   rightInv := by intro x; sorry_proof


namespace SciLean
-- use lean colls
export LeanColls (IndexType IndexType.card IndexType.univ IndexType.toFin IndexType.fromFin LawfulIndexType)
end SciLean

namespace IndexType

variable {ι : Type v} [IndexType ι]

open IndexType
@[simp]
theorem card_sum {ι κ} [IndexType ι] [IndexType κ] : card (ι ⊕ κ) = card ι + card κ := by rfl

@[simp]
theorem card_prod {ι κ} [IndexType ι] [IndexType κ] : card (ι × κ) = card ι * card κ := by rfl

@[simp]
theorem card_unit : card Unit = 1 := by rfl

instance (P : ι → Prop) [∀ i : ι, Decidable (P i)] : Decidable (∀ i : ι, P i) := Id.run do
  for i in IndexType.univ ι do
    if P i then
      continue
    else
      return .isFalse sorry_proof
  return .isTrue sorry_proof



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

def argValMax {I} [IndexType.{_,0} I] [Inhabited I]
    (f : I → X) [LT X] [∀ x x' : X, Decidable (x<x')] : I×X :=
  IndexType.reduceD
    (fun i => (i,f i))
    (fun (i,e) (i',e') => if e < e' then (i',e') else (i,e))
    (default, f default)

def argMax {I} [IndexType.{_,0} I] [Inhabited I]
    (f : I → X) [LT X] [∀ x x' : X, Decidable (x<x')] : I :=
  (IndexType.argValMax f).1


@[specialize] def sum {α : Type u} [Zero α] [Add α] (f : ι → α) : α :=
  Fold.fold (β:=α) (C:=IndexType.Univ ι) (τ:=ι) (IndexType.univ ι) (fun (s : α) (i : ι) => s + f i) (0 : α)

open Lean.TSyntax.Compat in
macro (priority:=high) " ∑ " xs:Lean.explicitBinders ", " b:term:66 : term => Lean.expandExplicitBinders ``sum xs b

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



open IndexType
@[rsimp guard I .notAppOf ``Fin]
theorem fold_linearize {I X : Type _} [IndexType I] [LawfulIndexType I] (init : X) (f : X → I → X) :
    Fold.fold (IndexType.univ I) f init
    =
    Fold.fold (IndexType.univ (Fin (IndexType.card I))) (fun x i => f x (IndexType.fromFin i)) init := sorry_proof


open IndexType in
@[rsimp guard I .notAppOf ``Fin]
theorem sum_linearize {I X : Type _} [Add X] [Zero X] [IndexType I] [LawfulIndexType I] (f : I → X) :
    ∑ i, f i
    =
    ∑ i : Fin (card I), f (fromFin i) := by simp only [sum]; rw[fold_linearize]
