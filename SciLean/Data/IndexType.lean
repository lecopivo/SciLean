import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Tactic.ProxyType
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith

import SciLean.Util.SorryProof
import SciLean.Tactic.RefinedSimp
import SciLean.Meta.SimpAttr

open Set

namespace SciLean

class Size {α : Sort u} (a : α) where
  size : Nat

export Size (size)

instance (a : List α) : Size a where
  size := a.length

instance (a : Array α) : Size a where
  size := a.size


------------------

class FirstLast {α : Sort u} (a : α) (β : outParam (Type v)) where
  /-- The first and the last element of a value or a type

  This function can be called on values
  ```
  firstLast? [1,2,3,4] = .some (1,4)
  ```
  and on types
  ```
  firstLast? (Fin n) = .some (⟨0,⋯⟩, ⟨n-1,⋯⟩)
  ```
  -/
  firstLast? : Option (β×β)

export FirstLast (firstLast?)

/-- The first element of of a value or a type.

This function can be called on values
```
first? [1,2,3,4] = .some 0
```
and on types
```
first? (Fin n) = .some ⟨0,⋯⟩
```
-/
def first? {α : Sort u} (a : α) [FirstLast a β] : Option β :=
  match FirstLast.firstLast? a with
  | .some (a,_) => .some a
  | .none => .none


/-- The last element of of a value or a type.

This function can be called on values
```
last? [1,2,3,4] = .some 4
```
and on types
```
last? (Fin n) = .some ⟨n-1,⋯⟩
```
-/
def last? {α : Sort u} (a : α) [FirstLast a β] : Option β :=
  match FirstLast.firstLast? a with
  | .some (_,b) => .some b
  | .none => .none


------------------


-- TODO: consider adding reverse versions `revfull` `revinterval
--       such that `.interval 5 0` is empty and should be represented by `revinterval 5 0`
--       also interval is closed on both sides
inductive IndexType.Range (I : Type u)
  /-- Empty range. -/
  | empty
  /-- Range over all elements. -/
  | full
  /-- Range starting from `a` and ending with `b` inclusive.

  In case `a` is larger then `b` then this range should run in reverse ordering. -/
  | interval (a b : I)

/-- Reverse range. -/
def IndexType.Range.reverse {I : Type u} (r : IndexType.Range I) [FirstLast I I] : IndexType.Range I :=
  match r with
  | .empty => empty
  | .full =>
    match FirstLast.firstLast? I with
    | .some (a,b) => .interval b a
    | .none => .empty
  | interval a b => .interval b a

@[inline]
def IndexType.Range.ofEquiv (f : I ≃ J) (i : Range I) : Range J :=
  match i with
  | .empty => .empty
  | .full => .full
  | .interval a b => .interval (f a) (f b)


@[inline]
def IndexType.Range.ofProd (i : Range (I×J)) : Range I × Range J :=
  match i with
  | .empty => (.empty, .empty)
  | .full => (.full, .full)
  | .interval (a,a') (b,b') => (.interval a b, .interval a' b')

open FirstLast in
@[inline]
def IndexType.Range.prod (i : Range I) (j : Range J) [FirstLast I I] [FirstLast J J] : Range (I×J) :=
  match i, j with
  | .empty, _ => .empty
  | _, .empty => .empty
  | .full, .full => .full
  | .interval a b, .interval a' b' => .interval (a,a') (b,b')
  | .interval a b, .full =>
    match firstLast? J with
    | .some (a',b') => .interval (a,a') (b,b')
    | .none => .empty
  | .full, .interval a' b' =>
    match firstLast? I with
    | .some (a,b) => .interval (a,a') (b,b')
    | .none => .empty


@[inline]
def IndexType.Range.ofSigma (i : Range ((_:I)×J)) : Range I × Range J :=
  match i with
  | .empty => (.empty, .empty)
  | .full => (.full, .full)
  | .interval ⟨a,a'⟩ ⟨b,b'⟩ => (.interval a b, .interval a' b')


open FirstLast in
@[inline]
def IndexType.Range.sprod (i : Range I) (j : Range J) [FirstLast I I] [FirstLast J J] : Range ((_:I)×J) :=
  match i, j with
  | .empty, _ => .empty
  | _, .empty => .empty
  | .full, .full => .full
  | .interval a b, .interval a' b' => .interval ⟨a,a'⟩ ⟨b,b'⟩
  | .interval a b, .full =>
    match firstLast? J with
    | .some (a',b') => .interval ⟨a,a'⟩ ⟨b,b'⟩
    | .none => .empty
  | .full, .interval a' b' =>
    match firstLast? I with
    | .some (a,b) => .interval ⟨a,a'⟩ ⟨b,b'⟩
    | .none => .empty



inductive IndexType.Stream (I : Type u) where
  /-- Stream for range `range` that has not been started -/
  | start (range : Range I)
  /-- Running stream with current value `val` and range `range`. -/
  | val (val : I) (range : Range I)
  -- /-- Stream that has been exhausted -/
  -- | done

@[inline]
def IndexType.Stream.val! [Inhabited I] (s : Stream I) : I :=
  match s with
  | .start _ => panic! "can't take value of start stream!"
  | .val i _ => i

@[inline]
def IndexType.Stream.ofEquiv (f : I ≃ J) (i : Stream I) : Stream J :=
  match i with
  | .start r => .start (r.ofEquiv f)
  | .val i r => .val (f i) (r.ofEquiv f)

@[inline]
def IndexType.Stream.ofProd (i : Stream (I×J)) : Stream I × Stream J :=
  match i with
  | .start r =>
    let (r,s) := r.ofProd
    (.start r, .start s)
  | .val (i,j) r =>
    let (r, s) := r.ofProd
    (.val i r, .val j s)

@[inline]
def IndexType.Stream.prod (i : Stream I) (j : Stream J) [FirstLast I I] [FirstLast J J] : Stream (I×J) :=
  match i, j with
  | .start ri, .start rj => .start (ri.prod rj)
  | .start ri, .val _ rj => .start (ri.prod rj)
  | .val _ ri, .start rj => .start (ri.prod rj)
  | .val i ri, .val j rj => .val (i,j) (ri.prod rj)


@[inline]
def IndexType.Stream.ofSigma (i : Stream ((_:I)×J)) : Stream I × Stream J :=
  match i with
  | .start r =>
    let (r,s) := r.ofSigma
    (.start r, .start s)
  | .val ⟨i,j⟩ r =>
    let (r, s) := r.ofSigma
    (.val i r, .val j s)


@[inline]
def IndexType.Stream.sprod (i : Stream I) (j : Stream J) [FirstLast I I] [FirstLast J J] :
    Stream ((_:I)×J) :=
  match i, j with
  | .start ri, .start rj => .start (ri.sprod rj)
  | .start ri, .val _ rj => .start (ri.sprod rj)
  | .val _ ri, .start rj => .start (ri.sprod rj)
  | .val i ri, .val j rj => .val ⟨i,j⟩ (ri.sprod rj)



-- This is alternative to LeanColls.IndexType which unfortunatelly has two universe parameters
-- and because of that it is very difficult to work with.
class IndexType (I : Type u) extends Fintype I, Stream (IndexType.Stream I) I, Size I, FirstLast I I where
  toFin : I → Fin size
  fromFin : Fin size → I
  -- TODO: add bunch of coherence conditions between differente fields

def fullRange (I : Type u) [IndexType I] : IndexType.Stream I := .start .full

-- def IndexType.first? (I : Type u) [IndexType I] : Option I := SciLean.first? I

instance [FirstLast I I] (r : IndexType.Range I) : FirstLast r I :=
  match r with
  | .empty => ⟨.none⟩
  | .full => ⟨FirstLast.firstLast? I⟩
  | .interval a b => ⟨.some (a,b)⟩


instance : IndexType Empty where
  size := 0
  toFin x := Empty.elim x
  fromFin i := by have := i.2; simp_all only [Nat.not_lt_zero]
  next? _ := .none
  firstLast? := .none


instance : IndexType Unit where
  size := 1
  toFin _ := 1
  fromFin _ := ()
  next? _ := .none
  firstLast? := .some ((),())


instance : IndexType Bool where
  size := 2
  toFin x := match x with | false => 0 | true => 1
  fromFin x := match x with | ⟨0,_⟩ => false | ⟨1,_⟩ => true
  firstLast? := .some (false, true)
  next? s :=
    match s with
    | .start r =>
      match r with
      | .empty => none
      | .full => .some (false, .val false r)
      | .interval a _ => .some (a, .val a r)

    | .val val r =>
      match r, val with
      | .empty, _ => .none
      | .full, false => .some (true, .val true r)
      | .full, true => .none
      | .interval a b, x =>
        if a = b
        then .none
        else if x = a
             then .some (b, .val b r)
             else .none


instance : IndexType (Fin n) where
  size := n
  toFin x := x
  fromFin x := x
  firstLast? :=
    if h : n ≠ 0 then
      .some (⟨0, by omega⟩, ⟨n-1,by omega⟩)
    else
      .none
  next? s :=
    match s with
    | .start r =>
      match r with
      | .empty => none
      | .full =>
        if h : n ≠ 0 then
          let x : Fin n := ⟨0, by omega⟩
          .some (x, .val x r)
        else
          .none
      | .interval a _ => .some (a, .val a r)

    | .val val r =>
      match r with
      | .empty => .none
      | .full =>
        if h : val.1 + 1 < n then
          let x := ⟨val.1+1,by omega⟩
          .some (x, .val x r)
        else
          .none
      | .interval a b =>
        if a.1 ≤ b.1 then
          if h : val.1 + 1 ≤ b.1 then
            let x := ⟨val.1+1,by omega⟩
            .some (x, .val x r)
          else
            .none
        else
          if h : b.1 + 1 ≤ val.1 then
            let x := ⟨val.1-1,by omega⟩
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
  firstLast? :=
    match FirstLast.firstLast? α, FirstLast.firstLast? β with
    | .some (a,a'), .some (b,b') => .some ((a,b),(a',b'))
    | _, _ => .none
  next? s :=
    match s with
    | .start r =>
      let (ri, rj) := r.ofProd
      match first? ri, first? rj with
      | .some i, .some j => .some ((i,j), .val (i,j) r)
      | _, _ => .none
    | .val (i,j) r =>
      let (ri,rj) := r.ofProd
      let si := IndexType.Stream.val i ri
      let sj := IndexType.Stream.val j rj
      match Stream.next? si with
      | .some (i', si) => .some ((i',j), si.prod sj)
      | .none =>
        match first? ri, Stream.next? sj with
        | .some i', .some (j', sj) => .some ((i',j'), (IndexType.Stream.val i' ri).prod sj)
        | _, _ => .none


instance {α β} [IndexType α] [IndexType β] : IndexType ((_ : α) × β) where
  size := size α * size β
  toFin := fun ⟨a,b⟩ => ⟨(IndexType.toFin a).1 + size α * (IndexType.toFin b).1, by sorry_proof⟩
  fromFin ij :=
    -- this choice will result in column major matrices
    let i : Fin (size α) := ⟨ij.1 % size α, by sorry_proof⟩
    let j : Fin (size β) := ⟨ij.1 / size α, by sorry_proof⟩
    ⟨IndexType.fromFin i, IndexType.fromFin j⟩
  firstLast? :=
    match FirstLast.firstLast? α, FirstLast.firstLast? β with
    | .some (a,a'), .some (b,b') => .some (⟨a,b⟩,⟨a',b'⟩)
    | _, _ => .none
  next? s :=
    match s with
    | .start r =>
      let (ri, rj) := r.ofSigma
      match first? ri, first? rj with
      | .some i, .some j => .some (⟨i,j⟩, .val ⟨i,j⟩ r)
      | _, _ => .none
    | .val ⟨i,j⟩ r =>
      let (ri,rj) := r.ofSigma
      let si := IndexType.Stream.val i ri
      let sj := IndexType.Stream.val j rj
      match Stream.next? si with
      | .some (i', si) => .some (⟨i',j⟩, si.sprod sj)
      | .none =>
        match first? ri, Stream.next? sj with
        | .some i', .some (j', sj) => .some (⟨i',j'⟩, (IndexType.Stream.val i' ri).sprod sj)
        | _, _ => .none


def IndexType.Range.ofSum [FirstLast α α] [FirstLast β β] (r : Range (α ⊕ β)) :
    (Range α × Range β) ⊕ (Range β × Range α) :=
  match r with
  | .empty => .inl (.empty, .empty)
  | .full => .inl (.full, .full)
  | .interval (.inl a) (.inl a') => .inl (.interval a a', .empty)
  | .interval (.inr b) (.inr b') => .inl (.empty, .interval b b')
  | .interval (.inl a) (.inr b') =>
    let a' := last? α |>.getD a
    let b := first? β |>.getD b'
    .inl (.interval a a', .interval b b')
  | .interval (.inr b) (.inl a') =>
    let a := last? α |>.getD a'
    let b' := first? β |>.getD b
    .inr (.interval b b', .interval a a')

instance {α β} [FirstLast α α] [FirstLast β β] : FirstLast (α ⊕ β) (α ⊕ β) where
  firstLast? :=
    match FirstLast.firstLast? α, FirstLast.firstLast? β with
    | .some (a,_), .some (_,b') => .some (.inl a, .inr b')
    | .some (a,a'), .none => .some (.inl a, .inl a')
    | .none, .some (b,b') => .some (.inr b, .inr b')
    | .none, .none => .none


-- todo: implement this and provide a better implementation of the following instance
def IndexType.Stream.ofSum [FirstLast α α] [FirstLast β β] (s : Stream (α ⊕ β)) :
    ((Stream α × Range β)) ⊕ ((Stream β × Range α)) := sorry


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
    -- there has to be a better implementation of this ...
    -- we should somehow use `IndexType.Stream.ofSum` and then combine them back together
    match s with
    | .start r =>
      match first? r with
      | .some x => .some (x, .val x r)
      | .none => .none
    | .val x r =>
      match x, r.ofSum with
      | .inl a, .inl (ra, rb) =>
        match Stream.next? (IndexType.Stream.val a ra) with
        | .some (a',_) => .some (.inl a', .val (.inl a') r)
        | .none =>
          match first? rb with
          | .some b' => .some (.inr b', .val (.inr b') r)
          | .none => .none
      | .inr b, .inl (_, rb) =>
        match Stream.next? (IndexType.Stream.val b rb) with
        | .some (b',_) => .some (.inr b', .val (.inr b') r)
        | .none => .none
      | .inl a, .inr (_, ra) =>
        match Stream.next? (IndexType.Stream.val a ra) with
        | .some (a',_) => .some (.inl a', .val (.inl a') r)
        | .none => .none
      | .inr b, .inr (rb, ra) =>
        match Stream.next? (IndexType.Stream.val b rb) with
        | .some (b',_) => .some (.inr b', .val (.inr b') r)
        | .none =>
          match first? ra with
          | .some a' => .some (.inl a', .val (.inl a') r)
          | .none => .none


instance (a b : Int) : IndexType (Icc a b) where
  size := ((b + 1) - a).toNat
  toFin i := ⟨(i.1 - a).toNat,
    by
      cases i; case mk i lt =>
        simp at lt ⊢; simp (disch:=aesop) only [Int.toNat_of_nonneg, sub_lt_sub_iff_right]; omega⟩
  fromFin i := ⟨a + i.1, by cases i; case mk i lt => simp at lt ⊢; omega⟩
  firstLast? :=
    if h :a ≤ b then
      .some (⟨a,by simpa⟩,⟨b, by simpa⟩)
    else
      .none
  next? s :=
    match s with
    | .start r =>
      match r with
      | .empty => none
      | .full =>
        if h : a ≤ b then
          let x : Icc a b := ⟨a, by simpa⟩
          .some (x, .val x r)
        else
          .none
      | .interval a' _ => .some (a', .val a' r)

    | .val val r =>
      match r with
      | .empty => .none
      | .full =>
        if h : val.1 + 1 ≤ b then
          have := val.2
          let x := ⟨val.1+1,by simp_all; omega⟩
          .some (x, .val x r)
        else
          .none
      | .interval c d =>
        if _ : c.1 ≤ d.1 then
          if h : val.1 + 1 ≤ b then
            have := val.2
            let x := ⟨val.1+1,by simp_all; omega⟩
            .some (x, .val x r)
          else
            .none
        else
          if h : d.1 + 1 ≤ val.1 then
            have := val.2; have := c.2;  have := d.2
            let x := ⟨val.1-1,by simp_all; omega⟩
            .some (x, .val x r)
          else
            .none


def IndexType.ofEquiv [IndexType I] [Fintype J] (f : I≃J) : IndexType J where
  size := size I
  toFin j := toFin (f.symm j)
  fromFin idx := f (fromFin idx)
  firstLast? :=
    match FirstLast.firstLast? I with
    | .some (a,b) => .some (f a, f b)
    | .none => none
  next? s :=
    match Stream.next? (s.ofEquiv f.symm) with
    | .some (i, si) => .some (f i, si.ofEquiv f)
    | .none => .none


open Lean Elab Command
def mkIndexTypeInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false -- mutually inductive types are not supported
  let id : Ident := mkIdent declNames[0]!
  try
    elabCommand (← `(deriving instance Fintype for $id))
  catch _ =>
    pure ()

  elabCommand (← `(instance : IndexType $id := IndexType.ofEquiv (proxy_equiv% $id)))
  return true

initialize
  registerDerivingHandler ``IndexType mkIndexTypeInstanceHandler


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
  if let .some i := first? ι then
    let mut a := f i
    for h : i in [1:size ι] do
      have := h.1
      have := h.2
      a ← op a (f (IndexType.fromFin ⟨i,by simp_all⟩))
    return a
  else
    return default

def reduceD (f : ι → α) (op : α → α → α) (default : α) : α := Id.run do
  if let .some i := first? ι then
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
