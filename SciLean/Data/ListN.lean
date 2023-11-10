import Lean 

structure ListN (α n) where
  val : List α
  property : val.length = n

namespace ListN


@[simp]
def map₂ (op : α → β → γ) (l : ListN α n) (l' : ListN β n) : ListN γ n :=
  match n, l, l' with
  | 0, ⟨[],_⟩, ⟨[], _⟩ => ⟨[], rfl⟩
  | n+1, ⟨x :: xs, hx⟩, ⟨y :: ys, hy⟩ => 
    let xs : ListN α n := ⟨xs, by simp at hx; exact hx⟩
    let ys : ListN β n := ⟨ys, by simp at hy; exact hy⟩
    let zs := map₂ op xs ys
    ⟨op x y :: zs.val, by simp; exact zs.property⟩


instance [Add α] : Add (ListN α n) := ⟨fun x y => x.map₂ (·+·) y⟩
instance [Sub α] : Sub (ListN α n) := ⟨fun x y => x.map₂ (·-·) y⟩
instance [Mul α] : Mul (ListN α n) := ⟨fun x y => x.map₂ (·*·) y⟩
instance [Div α] : Div (ListN α n) := ⟨fun x y => x.map₂ (·/·) y⟩


@[simp] 
theorem add_elemwise {n : Nat} [Add α]
  (x y : α) (xs ys : List α) (hx : xs.length = n) (hy : ys.length = n) 
  : (ListN.mk (n:=n+1) (x :: xs) (by simp; exact hx)) + (ListN.mk (y :: ys) (by simp; exact hy))
    =
    ListN.mk ((x + y) :: (ListN.mk xs hx + ListN.mk ys hy).1) (by simp; exact (ListN.mk xs hx + ListN.mk ys hy).2) := by rfl

@[simp]
theorem sub_elemwise {n : Nat} [Sub α]
  (x y : α) (xs ys : List α) (hx : xs.length = n) (hy : ys.length = n) 
  : (ListN.mk (n:=n+1) (x :: xs) (by simp; exact hx)) - (ListN.mk (y :: ys) (by simp; exact hy))
    =
    ListN.mk ((x - y) :: (ListN.mk xs hx - ListN.mk ys hy).1) (by simp; exact (ListN.mk xs hx - ListN.mk ys hy).2) := by rfl

@[simp] 
theorem mul_elemwise {n : Nat} [Mul α]
  (x y : α) (xs ys : List α) (hx : xs.length = n) (hy : ys.length = n) 
  : (ListN.mk (n:=n+1) (x :: xs) (by simp; exact hx)) * (ListN.mk (y :: ys) (by simp; exact hy))
    =
    ListN.mk ((x * y) :: (ListN.mk xs hx * ListN.mk ys hy).1) (by simp; exact (ListN.mk xs hx * ListN.mk ys hy).2) := by rfl

@[simp] 
theorem div_elemwise {n : Nat} [Div α]
  (x y : α) (xs ys : List α) (hx : xs.length = n) (hy : ys.length = n) 
  : (ListN.mk (n:=n+1) (x :: xs) (by simp; exact hx)) / (ListN.mk (y :: ys) (by simp; exact hy))
    =
    ListN.mk ((x / y) :: (ListN.mk xs hx / ListN.mk ys hy).1) (by simp; exact (ListN.mk xs hx / ListN.mk ys hy).2) := by rfl


--------------------------------------------------------------------------------
-- Notation --------------------------------------------------------------------
--------------------------------------------------------------------------------

open Lean in
/-- Notation for list literals with list lenght in its type. -/
macro "[" xs:term,* "]'" : term => do
  let n := Syntax.mkNumLit (toString xs.getElems.size)
  `(ListN.mk (n:=$n) [$xs,*] rfl)

@[app_unexpander ListN.mk]
def unexpandListNMk : Lean.PrettyPrinter.Unexpander
  | `($(_) [$xs,*] $_*) => 
    `([$xs,*]')
  | _  => throw ()
