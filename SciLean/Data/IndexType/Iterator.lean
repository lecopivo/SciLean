import SciLean.Data.IndexType.Range

namespace SciLean.IndexType

inductive Iterator (I : Type u) where
  /-- Iterator for range `range` that has not been started -/
  | start (range : Range I)
  /-- Running iterator with current value `val` and range `range`. -/
  | val (val : I) (range : Range I)
  -- /-- Iterator that has been exhausted -/
  -- | done

def _root_.SciLean.fullRange (I : Type u) : IndexType.Range I := .full
def _root_.SciLean.intervalRange {I : Type u} (a b : I) : IndexType.Range I := (.interval a b)

namespace Iterator

def val! [Inhabited I] (s : Iterator I) : I :=
  match s with
  | .start _ => panic! "can't take value of start iterator!"
  | .val i _ => i

def ofEquiv (f : I ≃ J) (i : Iterator I) : Iterator J :=
  match i with
  | .start r => .start (r.ofEquiv f)
  | .val i r => .val (f i) (r.ofEquiv f)

def ofProd (i : Iterator (I×J)) : Iterator I × Iterator J :=
  match i with
  | .start r =>
    let (r,s) := r.ofProd
    (.start r, .start s)
  | .val (i,j) r =>
    let (r, s) := r.ofProd
    (.val i r, .val j s)

def prod (i : Iterator I) (j : Iterator J) [FirstLast I I] [FirstLast J J] : Iterator (I×J) :=
  match i, j with
  | .start ri, .start rj => .start (ri.prod rj)
  | .start ri, .val _ rj => .start (ri.prod rj)
  | .val _ ri, .start rj => .start (ri.prod rj)
  | .val i ri, .val j rj => .val (i,j) (ri.prod rj)


def ofSigma (i : Iterator ((_:I)×J)) : Iterator I × Iterator J :=
  match i with
  | .start r =>
    let (r,s) := r.ofSigma
    (.start r, .start s)
  | .val ⟨i,j⟩ r =>
    let (r, s) := r.ofSigma
    (.val i r, .val j s)


def sprod (i : Iterator I) (j : Iterator J) [FirstLast I I] [FirstLast J J] :
    Iterator ((_:I)×J) :=
  match i, j with
  | .start ri, .start rj => .start (ri.sprod rj)
  | .start ri, .val _ rj => .start (ri.sprod rj)
  | .val _ ri, .start rj => .start (ri.sprod rj)
  | .val i ri, .val j rj => .val ⟨i,j⟩ (ri.sprod rj)


-- todo: implement this and provide a better implementation of IndexType instance for Sum
-- private def ofSum [FirstLast α α] [FirstLast β β] (s : Iterator (α ⊕ β)) :
--     ((Iterator α × Range β)) ⊕ ((Iterator β × Range α)) := sorry
