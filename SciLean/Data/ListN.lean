import Lean

inductive ListN (α : Type u) : Nat → Type u
  | nil : ListN α 0
  | cons {n} (x : α) (xs : ListN α n) : ListN α (n+1)

namespace ListN

def toList (l : ListN α n) : List α :=
  match l with
  | .nil => []
  | .cons x xs => x :: xs.toList

def toArray (l : ListN α n) : Array α := Id.run do
  let mut a : Array α := .mkEmpty n
  go a l
where
  go {m} (a : Array α) (l : ListN α m) : Array α :=
    match l with
    | .nil => a
    | .cons x xs => go (a.push x) xs

instance [ToString α] : ToString (ListN α n) := ⟨fun l => toString l.toList ++ "'"⟩


@[simp]
def map₂ (op : α → β → γ) (l : ListN α n) (l' : ListN β n) : ListN γ n :=
  match l, l' with
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (op x y) (map₂ op xs ys)


instance [Add α] : Add (ListN α n) := ⟨fun x y => x.map₂ (·+·) y⟩
instance [Sub α] : Sub (ListN α n) := ⟨fun x y => x.map₂ (·-·) y⟩
instance [Mul α] : Mul (ListN α n) := ⟨fun x y => x.map₂ (·*·) y⟩
instance [Div α] : Div (ListN α n) := ⟨fun x y => x.map₂ (·/·) y⟩


@[simp]
theorem add_elemwise {n : Nat} [Add α]
  (x y : α) (xs ys : ListN α n)
  : (ListN.cons x xs) + (ListN.cons y ys)
    =
    (ListN.cons (x+y) (xs + ys)) := by rfl

@[simp]
theorem sub_elemwise {n : Nat} [Sub α]
  (x y : α) (xs ys : ListN α n)
  : (ListN.cons x xs) - (ListN.cons y ys)
    =
    (ListN.cons (x-y) (xs - ys)) := by rfl

@[simp]
theorem mul_elemwise {n : Nat} [Mul α]
  (x y : α) (xs ys : ListN α n)
  : (ListN.cons x xs) * (ListN.cons y ys)
    =
    (ListN.cons (x*y) (xs * ys)) := by rfl

@[simp]
theorem div_elemwise {n : Nat} [Div α]
  (x y : α) (xs ys : ListN α n)
  : (ListN.cons x xs) / (ListN.cons y ys)
    =
    (ListN.cons (x/y) (xs / ys)) := by rfl


--------------------------------------------------------------------------------
-- Notation --------------------------------------------------------------------
--------------------------------------------------------------------------------

/-- Notation for list literals with list lenght in its type. -/
syntax "[" term,* "]'" : term

open Lean in
macro_rules
| `(term| []') => `(ListN.nil)
| `(term| [$x:term]') => `(ListN.cons $x .nil)
| `(term| [$x:term, $xs:term,*]') => do
  let n := Syntax.mkNumLit (toString xs.getElems.size)
  `(ListN.cons (n:=$n) $x [$xs,*]')

@[app_unexpander ListN.nil]
def unexpandListNNil : Lean.PrettyPrinter.Unexpander
  | `($(_)) =>
    `([]')

@[app_unexpander ListN.cons]
def unexpandListNCons : Lean.PrettyPrinter.Unexpander
  | `($(_) $x []') =>
    `([$x]')
  | `($(_) $x [$xs',*]') =>
    `([$x, $xs',*]')
  | _  => throw ()
