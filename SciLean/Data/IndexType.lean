import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical

import SciLean.Util.SorryProof
import SciLean.Tactic.RefinedSimp
import SciLean.Meta.SimpAttr

open Set

namespace SciLean

class Size {α : Sort u} (a : α) where
  size : Nat

export Size (size)

instance (a : Array α) : Size a where
  size := a.size

instance (a : List α) : Size a where
  size := a.length

inductive IndexType.Range (I : Type u)
  | full

inductive IndexType.Stream (I : Type u) where
  /-- Stream for range `range` that has not been started -/
  | start (range : Range I)
  /-- Running stream with current value `val` and range `range`. -/
  | val (val : I) (range : Range I)
  -- /-- Stream that has been exhausted -/
  -- | done

-- This is alternative to LeanColls.IndexType which unfortunatelly has two universe parameters
-- and because of that it is very difficult to work with.
class IndexType (I : Type u) extends Fintype I, Stream (IndexType.Stream I) I, Size I where
  toFin : I → Fin size
  fromFin : Fin size → I

def fullRange (I : Type u) [IndexType I] : IndexType.Stream I := .start .full

def IndexType.first? (I : Type u) [IndexType I] : Option I :=
  if h : size I ≠ 0 then
    .some (IndexType.fromFin ⟨0, by omega⟩)
  else
    .none




instance : IndexType Empty where
  size := 0
  toFin x := Empty.elim x
  fromFin i := by have := i.2; simp_all only [Nat.not_lt_zero]
  next? _ := .none

instance : IndexType Unit where
  size := 1
  toFin _ := 1
  fromFin _ := ()
  next? _ := .none

instance : IndexType Bool where
  size := 2
  toFin x := match x with | false => 0 | true => 1
  fromFin x := match x with | ⟨0,_⟩ => false | ⟨1,_⟩ => true
  next? s :=
    match s with
    | .start r => .some (false, .val false r)
    | .val val r =>
      match val with
      | false => .some (true, .val true r)
      | true => .none

instance : IndexType (Fin n) where
  size := n
  toFin x := x
  fromFin x := x
  next? s :=
    match s with
    | .start r =>
      if h : n ≠ 0 then
        let x : Fin n := ⟨0, by omega⟩
        .some (x, .val x r)
      else
        .none
    | .val val r =>
      if h : val.1 + 1 < n then
        let x := ⟨val.1+1,by omega⟩
        .some (x, .val x r)
      else
        .none


instance {α β} [IndexType α] [IndexType β] : IndexType (α × β) where
  size := size α * size β
  toFin := fun (a,b) => ⟨(IndexType.toFin a).1 + size α * (IndexType.toFin b).1, by sorry_proof⟩
  fromFin ij :=
    -- this choice will result in column major matrices
    let i : Fin (size α) := ⟨ij.1 % size α, by sorry_proof⟩
    let j : Fin (size β) := ⟨ij.1 / size α, by sorry_proof⟩
    (IndexType.fromFin i, IndexType.fromFin j)
  next? s :=
    match s with
    | .start _r =>
      if let .some a := IndexType.first? α then
        if let .some b := IndexType.first? β then
          .some ((a,b), .val (a,b) .full) -- todo: split the range somehow
        else
          .none
      else
        .none
    | .val (a,b) _r =>
      if let .some sa := Stream.next? (IndexType.Stream.val a .full) then
        .some ((sa.1,b), .val (sa.1,b) .full)
      else
        if let .some sb := Stream.next? (IndexType.Stream.val b .full) then
          if let .some a := IndexType.first? α then
            .some ((a,sb.1), .val (a,sb.1) .full)
          else
            .none
        else
          .none

instance {α β} [IndexType α] [IndexType β] : IndexType ((_ : α) × β) where
  size := size α * size β
  toFin := fun ⟨a,b⟩ => ⟨(IndexType.toFin a).1 + size α * (IndexType.toFin b).1, by sorry_proof⟩
  fromFin ij :=
    -- this choice will result in column major matrices
    let i : Fin (size α) := ⟨ij.1 % size α, by sorry_proof⟩
    let j : Fin (size β) := ⟨ij.1 / size α, by sorry_proof⟩
    ⟨IndexType.fromFin i, IndexType.fromFin j⟩
  next? s :=
    match s with
    | .start _r =>
      if let .some a := IndexType.first? α then
        if let .some b := IndexType.first? β then
          .some (⟨a,b⟩, .val ⟨a,b⟩ .full) -- todo: split the range somehow
        else
          .none
      else
        .none
    | .val ⟨a,b⟩ _r =>
      if let .some sa := Stream.next? (IndexType.Stream.val a .full) then
        .some (⟨sa.1,b⟩, .val ⟨sa.1,b⟩ .full)
      else
        if let .some sb := Stream.next? (IndexType.Stream.val b .full) then
          if let .some a := IndexType.first? α then
            .some (⟨a,sb.1⟩, .val ⟨a,sb.1⟩ .full)
          else
            .none
        else
          .none

instance {α β} [IndexType α] [IndexType β] : IndexType (α ⊕ β) where
  size := size α + size β
  toFin := fun ab =>
    match ab with
    | .inl a => ⟨(IndexType.toFin a).1, by sorry_proof⟩
    | .inr b => ⟨size α + (IndexType.toFin b).1, by sorry_proof⟩
  fromFin ij :=
    if ij.1 < size α then
      .inl (IndexType.fromFin ⟨ij.1, sorry_proof⟩)
    else
      .inr (IndexType.fromFin ⟨ij.1 - size α, sorry_proof⟩)
  next? s :=
    match s with
    | .start _r =>
      if let .some a := IndexType.first? α then
        .some (.inl a, .val (.inl a) .full)
      else
        if let .some b := IndexType.first? β then
          .some (.inr b, .val (.inr b) .full)
        else
          .none
    | .val x _r =>
      match x with
      | .inl a =>
        if let .some sa := Stream.next? (IndexType.Stream.val a .full) then
          .some (.inl sa.1, .val (.inl sa.1) .full)
        else
          if let .some b := IndexType.first? β  then
            .some (.inr b, .val (.inr b) .full)
          else
            .none
      | .inr b =>
        if let .some sb := Stream.next? (IndexType.Stream.val b .full) then
          .some (.inr sb.1, .val (.inr sb.1) .full)
        else
          .none

-- todo: if we want to have instances like `IndexType (Fin 4 → Fin 10)` then
--       `IndexType.Stream (Fin 4 → Fin 10)` should not hold element of `Fin 4 → Fin 10` but some
--       kind of array holding all the values
-- instance {α β} [IndexType α] [IndexType β] : IndexType (α → β) where
--   size := size β ^ size α
--   toFin := sorry
--   fromFin := sorry
--   next? := sorry

instance (a b : Int) : IndexType (Icc a b) where
  size := ((b + 1) - a).toNat
  toFin i := ⟨(i.1 - a).toNat,
    by
      cases i; case mk i lt =>
        simp at lt ⊢; simp (disch:=aesop) only [Int.toNat_of_nonneg, sub_lt_sub_iff_right]; omega⟩
  fromFin i := ⟨a + i.1, by cases i; case mk i lt => simp at lt ⊢; omega⟩
  next? s :=
    match s with
    | .start r =>
      if h : a ≤ b then
        .some (⟨a, by simpa⟩, .val ⟨a, by simpa⟩ r)
      else
        .none
    | .val x r =>
      if h : x.1 + 1 ≤ b then
        let x := ⟨x.1+1,by simp; constructor; sorry_proof; omega⟩
        .some (x, .val x r)
      else
        .none


namespace SciLean
end SciLean

namespace IndexType

variable {ι : Type v} [IndexType ι]

open IndexType
@[simp, simp_core]
theorem size_sum {ι κ} [IndexType ι] [IndexType κ] : size (ι ⊕ κ) = size ι + size κ := by rfl

@[simp, simp_core]
theorem size_prod {ι κ} [IndexType ι] [IndexType κ] : size (ι × κ) = size ι * size κ := by rfl

@[simp, simp_core]
theorem size_unit : size Unit = 1 := by rfl

@[simp, simp_core]
theorem size_fin (n : Nat) : size (Fin n) = n := by rfl

@[simp, simp_core]
theorem toFin_Fin (i : Fin n) :
    IndexType.toFin i = i :=
  rfl

@[simp, simp_core]
theorem fromFin_toFin {I} [IndexType I] (i : I) :
  fromFin (toFin i) = i := sorry_proof

@[simp, simp_core]
theorem toFin_fromFin {I} [IndexType I] (i : Fin (size I)) :
  toFin (fromFin (I:=I) i) = i := sorry_proof

-- instance (P : ι → Prop) [∀ i : ι, Decidable (P i)] : Decidable (∀ i : ι, P i) := Id.run do
--   for i in IndexType.univ ι do
--     if P i then
--       continue
--     else
--       return .isFalse sorry_proof
--   return .isTrue sorry_proof

def foldlM {m} [Monad m] (op : α → ι → m α) (init : α) : m α := do
  let mut a := init
  for i in fullRange ι do
    a ← op a i
  return a

def foldl (op : α → ι → α) (init : α) : α := Id.run do
  foldlM op init

def reduceMD {m} [Monad m] (f : ι → α) (op : α → α → m α) (default : α) : m α := do
  if let .some i := IndexType.first? ι then
    let mut a := f i
    for h : i in [1:size ι] do
      have := h.1
      have := h.2
      a ← op a (f (IndexType.fromFin ⟨i,by simp_all⟩))
    return a
  else
    return default

def reduceD (f : ι → α) (op : α → α → α) (default : α) : α := Id.run do
  if let .some i := IndexType.first? ι then
    let mut a := f i
    for h : i in [1:size ι] do
      have := h.1
      have := h.2
      a := op a (f (IndexType.fromFin ⟨i,by simp_all⟩))
    return a
  else
    return default

abbrev reduce [Inhabited α] (f : ι → α) (op : α → α → α) : α :=
  reduceD f op default

def argValMax {I} [IndexType I] [Inhabited I]
    (f : I → X) [LT X] [∀ x x' : X, Decidable (x<x')] : I×X :=
  IndexType.reduceD
    (fun i => (i,f i))
    (fun (i,e) (i',e') => if e < e' then (i',e') else (i,e))
    (default, f default)

def argMax {I} [IndexType I] [Inhabited I]
    (f : I → X) [LT X] [∀ x x' : X, Decidable (x<x')] : I :=
  (IndexType.argValMax f).1

@[specialize] def sum {α : Type u} [Zero α] [Add α] (f : ι → α) : α :=
  IndexType.reduceD f (fun (s : α) a => s + a) (0 : α)

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
  IndexType.reduceD f (fun (s : α) a => s * a) 1

open Lean.TSyntax.Compat in
macro (priority:=high) " ∏ " xs:Lean.explicitBinders ", " b:term:66 : term => Lean.expandExplicitBinders ``product xs b

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
theorem reduce_linearize {I X : Type _} [IndexType I] (init : X) (f : I → X) (op : X → X → X) :
    IndexType.reduceD f op init
    =
    IndexType.reduceD (fun i : Fin (size I) => f (fromFin i)) op init := sorry_proof


@[sum_push]
theorem sum_pair {I X : Type _} [Add X] [Zero X] [Add Y] [Zero Y] [IndexType I]
    (f : I → X) (g : I → Y) :
    ∑ i, (f i, g i) = (∑ i, f i, ∑ i, g i) := sorry_proof

@[sum_pull]
theorem pair_sum {I X : Type _} [Add X] [Zero X] [Add Y] [Zero Y] [IndexType I]
    (f : I → X) (g : I → Y) :
    (∑ i, f i, ∑ i, g i) = ∑ i, (f i, g i) := sorry_proof


open IndexType in
@[rsimp guard I .notAppOf ``Fin]
theorem sum_linearize {I X : Type _} [Add X] [Zero X] [IndexType I] (f : I → X) :
    ∑ i, f i
    =
    ∑ i : Fin (size I), f (fromFin i) := by simp only [sum]; rw[reduce_linearize]


variable {I} [IndexType I]


section OnMonoid
variable [AddCommMonoid α]

@[add_pull, sum_push]
theorem sum_add_distrib (f g : I → α) : ∑ i , (f i + g i) = (∑ i, f i) + (∑ i, g i) := sorry_proof

@[add_push, sum_pull]
theorem add_sum (f g : I → α) : (∑ i, f i) + (∑ i, g i) = ∑ i , (f i + g i) := by simp only[add_pull]

end OnMonoid



section OnSemiring
variable [NonUnitalNonAssocSemiring α]

@[sum_pull, mul_push]
theorem sum_mul (f : I → α) (a : α) :
    (∑ i, f i) * a = ∑ i, f i * a := sorry_proof

@[sum_pull, mul_push]
theorem mul_sum (f : ι → α) (a : α) :
    a * ∑ i, f i = ∑ i, a * f i := sorry_proof

end OnSemiring
