import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Data.Int.Interval

import SciLean.Data.IndexType.Iterator
import SciLean.Util.SorryProof

namespace SciLean

open Function

class IndexType (I : Type u)
  extends Fintype I, Stream (IndexType.Iterator I) I, Size I, FirstLast I I
where
  toFin : I → Fin size
  fromFin : Fin size → I
  /-- Number of elements in a given range -/
  rangeSize : IndexType.Range I → Nat
  left_inv : LeftInverse fromFin toFin
  right_inv : RightInverse fromFin toFin
  first_last :
    (size = 0 ∧ firstLast? = none)
    ∨
    ((_ : size ≠ 0) → firstLast? = some (fromFin ⟨0,by omega⟩, fromFin ⟨size - 1, by omega⟩))
  -- TODO: add something about Iterators such that calling `next?` gives you one more element
  -- TODO: add condition on rangeSize function

open IndexType in
def finEquiv (I : Type u) [IndexType I] : I ≃ Fin (size I) where
  toFun := toFin
  invFun := fromFin
  left_inv := left_inv
  right_inv := right_inv


namespace IndexType

instance {ι} [IndexType ι] (r : Range ι) : Size r where
  size := rangeSize r

def fromNat {ι} [IndexType ι] (n : Nat) (h : n < size ι := by first | omega | simp_all; omega) : ι :=
  fromFin ⟨n, h⟩

----------------------------------------------------------------------------------------------------
-- Instances ---------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

instance [FirstLast I I] (r : Range I) : FirstLast r I :=
  match r with
  | .empty => ⟨.none⟩
  | .full => ⟨FirstLast.firstLast? I⟩
  | .interval a b => ⟨.some (a,b)⟩


instance : IndexType Empty where
  toFin x := Empty.elim x
  fromFin i := by have := i.2; aesop
  rangeSize := fun _ => 0
  next? _ := .none
  left_inv := by intro x; aesop
  right_inv := sorry_proof
  first_last := sorry_proof


instance : IndexType Unit where
  toFin _ := 1
  fromFin _ := ()
  rangeSize := fun r => match r with | .empty => 0 | .full | .interval _ _ => 1
  next? _ := .none
  left_inv := by intro; aesop
  right_inv := by intro; aesop
  first_last := by aesop


instance : IndexType Bool where
  size := 2
  toFin x := match x with | false => 0 | true => 1
  fromFin x := match x with | ⟨0,_⟩ => false | ⟨1,_⟩ => true
  rangeSize := fun r =>
    match r with
    | .empty => 0
    | .full => 2
    | .interval a b => if a = b then 1 else 2
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
  left_inv := by intro; aesop
  right_inv := by intro; aesop
  first_last := by aesop


instance : IndexType (Fin n) where
  toFin x := x
  fromFin x := x
  rangeSize := fun r =>
    match r with
    | .empty => 0
    | .full => n
    | .interval a b => if a.1 ≤ b.1 then (b.1 - a.1) + 1 else (a.1 - b.1) + 1
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
  left_inv := by intro; aesop
  right_inv := by intro; aesop
  first_last := by simp[firstLast?]; aesop



instance {α β} [IndexType α] [IndexType β] : IndexType (α × β) where
  toFin := fun (a,b) => ⟨(toFin a).1 + size α * (toFin b).1, by sorry_proof⟩
  fromFin ij :=
    -- this choice will result in column major matrices
    let i : Fin (size α) := ⟨ij.1 % size α, by sorry_proof⟩
    let j : Fin (size β) := ⟨ij.1 / size α, by sorry_proof⟩
    (fromFin i, fromFin j)
  rangeSize := fun r =>
    match r with
    | .empty => 0
    | .full => rangeSize (.full : Range α) * rangeSize (.full : Range β)
    | .interval (a,b) (a',b') => rangeSize (.interval a a') * rangeSize (.interval b b')
  next? s :=
    match s with
    | .start r =>
      let (ri, rj) := r.ofProd
      match first? ri, first? rj with
      | .some i, .some j => .some ((i,j), .val (i,j) r)
      | _, _ => .none
    | .val (i,j) r =>
      let (ri,rj) := r.ofProd
      let si := Iterator.val i ri
      let sj := Iterator.val j rj
      match Stream.next? si with
      | .some (i', si) => .some ((i',j), si.prod sj)
      | .none =>
        match first? ri, Stream.next? sj with
        | .some i', .some (j', sj) => .some ((i',j'), (Iterator.val i' ri).prod sj)
        | _, _ => .none
  left_inv := by intro; sorry_proof
  right_inv := by intro; sorry_proof
  first_last := by simp[firstLast?]; sorry_proof


instance {α β} [IndexType α] [IndexType β] : IndexType ((_ : α) × β) where
  toFin := fun ⟨a,b⟩ => ⟨(toFin a).1 + size α * (toFin b).1, by sorry_proof⟩
  fromFin ij :=
    -- this choice will result in column major matrices
    let i : Fin (size α) := ⟨ij.1 % size α, by sorry_proof⟩
    let j : Fin (size β) := ⟨ij.1 / size α, by sorry_proof⟩
    ⟨fromFin i, fromFin j⟩
  rangeSize := fun r =>
    match r with
    | .empty => 0
    | .full => rangeSize (.full : Range α) * rangeSize (.full : Range β)
    | .interval ⟨a,b⟩ ⟨a',b'⟩ => rangeSize (.interval a a') * rangeSize (.interval b b')
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
      let si := Iterator.val i ri
      let sj := Iterator.val j rj
      match Stream.next? si with
      | .some (i', si) => .some (⟨i',j⟩, si.sprod sj)
      | .none =>
        match first? ri, Stream.next? sj with
        | .some i', .some (j', sj) => .some (⟨i',j'⟩, (Iterator.val i' ri).sprod sj)
        | _, _ => .none
  left_inv := by intro; sorry_proof
  right_inv := by intro; sorry_proof
  first_last := by sorry_proof



instance {α β} [IndexType α] [IndexType β] : IndexType (α ⊕ β) where
  toFin := fun ab =>
    match ab with
    | .inl a => ⟨(toFin a).1, by sorry_proof⟩
    | .inr b => ⟨size α + (toFin b).1, by sorry_proof⟩
  fromFin ij :=
    if h : ij.1 < size α then
      .inl (fromNat ij.1)
    else
      .inr (fromNat (ij.1 - size α))
  rangeSize := fun r =>
    match r with
    | .empty => 0
    | .full => rangeSize (.full : Range α) + rangeSize (.full : Range β)
    | .interval (.inl a) (.inl a') => rangeSize (.interval a a')
    | .interval (.inr b) (.inr b') => rangeSize (.interval b b')
    | .interval (.inl a) (.inr b') | .interval (.inr b') (.inl a) =>
      let b := first? β |>.getD b'
      let a' := last? α |>.getD a
      rangeSize (.interval a a') + rangeSize (.interval b b')
  next? s :=
    -- there has to be a better implementation of this ...
    -- we should somehow use `Iterator.ofSum` and then combine them back together
    match s with
    | .start r =>
      match first? r with
      | .some x => .some (x, .val x r)
      | .none => .none
    | .val x r =>
      match x, r.ofSum with
      | .inl a, .inl (ra, rb) =>
        match Stream.next? (Iterator.val a ra) with
        | .some (a',_) => .some (.inl a', .val (.inl a') r)
        | .none =>
          match first? rb with
          | .some b' => .some (.inr b', .val (.inr b') r)
          | .none => .none
      | .inr b, .inl (_, rb) =>
        match Stream.next? (Iterator.val b rb) with
        | .some (b',_) => .some (.inr b', .val (.inr b') r)
        | .none => .none
      | .inl a, .inr (_, ra) =>
        match Stream.next? (Iterator.val a ra) with
        | .some (a',_) => .some (.inl a', .val (.inl a') r)
        | .none => .none
      | .inr b, .inr (rb, ra) =>
        match Stream.next? (Iterator.val b rb) with
        | .some (b',_) => .some (.inr b', .val (.inr b') r)
        | .none =>
          match first? ra with
          | .some a' => .some (.inl a', .val (.inl a') r)
          | .none => .none
  left_inv := by intro; sorry_proof
  right_inv := by intro; sorry_proof
  first_last := by sorry_proof


open Set in
instance (a b : Int) : IndexType (Icc a b) where
  size := size (Icc a b) -- why do we do we need to specify this?
  toFin i := ⟨(i.1 - a).toNat, sorry_proof⟩
  fromFin i := ⟨a + i.1, sorry_proof⟩
  rangeSize := fun r =>
    match r with
    | .empty => 0
    | .full => (b-a).toNat + 1
    | .interval c d => |d.1 - c.1|.toNat + 1
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
  left_inv := sorry_proof
  right_inv := sorry_proof
  first_last := sorry_proof



----------------------------------------------------------------------------------------------------
-- Basic properties --------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

variable {ι : Type v} [IndexType ι]


@[simp, simp_core]
theorem toFin_Fin (i : Fin n) :
    toFin i = i :=
  rfl

@[simp, simp_core]
theorem fromFin_toFin {I} [IndexType I] (i : I) :
  fromFin (toFin i) = i := sorry_proof

@[simp, simp_core]
theorem toFin_fromFin {I} [IndexType I] (i : Fin (size I)) :
  toFin (fromFin (I:=I) i) = i := sorry_proof
