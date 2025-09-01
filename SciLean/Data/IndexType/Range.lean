import Mathlib.Logic.Equiv.Defs

import SciLean.Data.IndexType.Init

namespace SciLean.IndexType


-- TODO: consider adding reverse versions `revfull` `revinterval
--       such that `.interval 5 0` is empty and should be represented by `revinterval 5 0`
--       also interval is closed on both sides
/-- Range specifying an interval of `I` that we can iterate over using `Stream` -/
inductive Range (I : Type u)
  /-- Empty range. -/
  | empty
  /-- Range over all elements. -/
  | full
  /-- Range starting from `a` and ending with `b` inclusive.

  In case `a` is larger then `b` then this range should run in reverse ordering. -/
  | interval (a b : I)


def _root_.SciLean.fullRange (I : Type*) : Range I := .full
def _root_.SciLean.intervalRange {I : Type*} (a b : I) : Range I := .interval a b

namespace Range

/-- Reverse range. -/
def reverse {I : Type u} (r : Range I) [FirstLast I I] : Range I :=
  match r with
  | .empty => empty
  | .full =>
    match firstLast? I with
    | .some (a,b) => .interval b a
    | .none => .empty
  | interval a b => .interval b a

@[inline]
def ofEquiv (f : I ≃ J) (i : Range I) : Range J :=
  match i with
  | .empty => .empty
  | .full => .full
  | .interval a b => .interval (f a) (f b)



-- @[inline] -- inlining breaks the current compiler on tests in `Test/indextype/ranges.lean`
def ofProd (i : Range (I×J)) : Range I × Range J :=
  match i with
  | .empty => (.empty, .empty)
  | .full => (.full, .full)
  | .interval (a,a') (b,b') => (.interval a b, .interval a' b')

open FirstLast in
-- @[inline] -- inlining breaks the current compiler on tests in `Test/indextype/fold.lean`
def prod (i : Range I) (j : Range J) [FirstLast I I] [FirstLast J J] : Range (I×J) :=
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
def ofSigma (i : Range ((_:I)×J)) : Range I × Range J :=
  match i with
  | .empty => (.empty, .empty)
  | .full => (.full, .full)
  | .interval ⟨a,a'⟩ ⟨b,b'⟩ => (.interval a b, .interval a' b')


open FirstLast in
@[inline]
def sprod (i : Range I) (j : Range J) [FirstLast I I] [FirstLast J J] :
    Range ((_:I)×J) :=
  match i.prod j with
  | .empty => .empty
  | .full => .full
  | .interval (a,b) (a',b') => .interval ⟨a,b⟩ ⟨a',b'⟩

def ofSum [FirstLast α α] [FirstLast β β] (r : Range (α ⊕ β)) :
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
